#![deny(missing_docs)]
use super::{append_container, container};
use crate::boxedmap::HashMap;
use alloc::boxed::Box;
use append_only_vec::AppendOnlyVec;
use core::{
    borrow::Borrow,
    convert::AsRef,
    fmt::{Debug, Display, Pointer},
    hash::{Hash, Hasher},
    num::NonZeroU32,
    ops::Deref,
};

#[cfg(feature = "std")]
use std::{ffi::OsStr, path::Path};

#[cfg(test)]
use alloc::string::{String, ToString};

#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[cfg(feature = "tinyset")]
use tinyset::Fits64;

#[cfg_attr(docsrs, doc(cfg(feature = "intern")))]
/// A small reference to an interned object.
///
/// The interned object will be held in memory indefinitely.  On the plus side,
/// this means that lifetime issues are simple when using `Intern32`.  It is
/// also slower to dereference than other intern types, since it uses an
/// additional layer of indirection to enable `Intern32` to be just a 32-bit
/// value.
///
/// # Example
/// ```rust
/// use internment::Intern32;
///
/// let x = Intern32::new("hello");
/// let y = Intern32::new("world");
/// assert_ne!(x, y);
/// assert_eq!(x, Intern32::new("hello"));
/// assert_eq!(*x, "hello"); // dereference an Intern32 like a pointer
/// ```
///
/// # Example with owned `String` data
///
/// ```rust
/// use internment::Intern32;
///
/// let x = Intern32::new("hello".to_string());
/// let y = Intern32::<String>::from_ref("world");
/// assert_ne!(x, y);
/// assert_eq!(x, Intern32::from_ref("hello"));
/// assert_eq!(y, Intern32::from_ref("world"));
/// assert_eq!(&*x, "hello"); // dereference a Intern32 like a pointer
/// ```
pub struct Intern32<T: 'static + ?Sized> {
    index: NonZeroU32,
    _phantom: std::marker::PhantomData<T>,
}

#[test]
fn like_doctest_intern() {
    let x = Intern32::new("hello".to_string());
    let y = Intern32::<String>::from_ref("world");
    assert_ne!(x, y);
    assert_eq!(x, Intern32::from_ref("hello"));
    assert_eq!(y, Intern32::from_ref("world"));
    assert_eq!(&*x, "hello"); // dereference a Intern like a pointer\
    let _ = Intern32::<String>::from_ref("Fortunato");
    assert!(Intern32::<String>::is_interned("Fortunato"));
    assert!(!Intern32::<String>::is_interned("Montresor"));
}

#[cfg(feature = "deepsize")]
impl<T: 'static + ?Sized> deepsize::DeepSizeOf for Intern32<T> {
    fn deep_size_of_children(&self, _context: &mut deepsize::Context) -> usize {
        0
    }
}

impl<T: Eq + Hash + Send + Sync + 'static + deepsize::DeepSizeOf> Intern32<T> {
    #[cfg_attr(docsrs, doc(cfg(all(feature = "deepsize", feature = "intern32"))))]
    /// Return the memory used by all interned objects of the given type.
    #[cfg(feature = "deepsize")]
    pub fn deep_size_of_interned() -> usize {
        use deepsize::DeepSizeOf;
        let set_size = INTERN_CONTAINERS
            .with(|m: &mut HashMap<&'static T, NonZeroU32>| -> usize { (*m).deep_size_of() });
        let data = INTERN_DATA.get::<AppendOnlyVec<Box<T>>>();
        struct Dummy<T: 'static>(&'static AppendOnlyVec<Box<T>>);
        impl<T: DeepSizeOf> deepsize::DeepSizeOf for Dummy<T> {
            fn deep_size_of_children(&self, context: &mut deepsize::Context) -> usize {
                self.0
                    .iter()
                    .map(|v| std::mem::size_of_val(v) + v.deep_size_of_children(context))
                    .sum::<usize>()
            }
        }
        let data_size = Dummy(data).deep_size_of();
        std::println!("XXXXXXXXXXXXXXXXX set {set_size} data {data_size}");
        set_size + data_size
    }
}

#[test]
fn has_niche() {
    assert_eq!(
        core::mem::size_of::<Intern32<String>>(),
        core::mem::size_of::<u32>(),
    );
    assert_eq!(
        core::mem::size_of::<Option<Intern32<String>>>(),
        core::mem::size_of::<u32>(),
    );
}

impl<T: ?Sized> Clone for Intern32<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

/// An `Intern` is `Copy`, which is unusual for a pointer.  This is safe
/// because we never free the data pointed to by an `Intern`.
impl<T: ?Sized> Copy for Intern32<T> {}

impl<T: ?Sized + Send + Sync> Intern32<T> {
    #[inline(always)]
    fn get_pointer(&self) -> *const T {
        &*self.get_my_ref()
    }
}

static INTERN_DATA: append_container::Arena = append_container::Arena::new();
static INTERN_CONTAINERS: container::Arena = container::Arena::new();

macro_rules! from_via_box {
    ($t:ty) => {
        impl From<&$t> for Intern32<$t> {
            #[inline]
            fn from(val: &$t) -> Self {
                Self::via_box(val)
            }
        }
    };
}
from_via_box!(core::ffi::CStr);
from_via_box!(str);
#[cfg(feature = "std")]
from_via_box!(std::path::Path);
impl<T: Eq + Hash + Send + Sync + 'static + Copy> From<&[T]> for Intern32<[T]> {
    #[inline]
    fn from(val: &[T]) -> Self {
        Self::via_box(val)
    }
}

impl<T: Eq + Hash + Send + Sync + 'static + Copy, const N: usize> From<&[T; N]> for Intern32<[T]> {
    /// Converts a `[T; N]` into a `Intern<[T]>`
    #[inline]
    fn from(val: &[T; N]) -> Self {
        Self::via_box(val)
    }
}

macro_rules! create_intern {
    ($t:ty, $borrow:expr, $box:expr) => {
        INTERN_CONTAINERS.with(|m: &mut HashMap<&'static $t, NonZeroU32>| -> Self {
            let index = m.get($borrow).copied().unwrap_or_else(|| {
                let v = INTERN_DATA.get::<AppendOnlyVec<Box<T>>>();
                let idx = v.push($box);
                let index = NonZeroU32::new(idx as u32 + 1).unwrap();
                m.insert(&v[idx], index);
                index
            });
            Intern32 {
                index,
                _phantom: std::marker::PhantomData,
            }
        })
    };
}

impl<T: Eq + Hash + Send + Sync + 'static + ?Sized> Intern32<T> {
    /// This method to be used internally
    fn via_box<'a, I>(val: &'a I) -> Self
    where
        Box<T>: From<&'a I>,
        I: Borrow<T> + ?Sized,
    {
        create_intern!(T, val.borrow(), Box::from(val))
    }
}

impl<T: Eq + Hash + Send + Sync + 'static + ?Sized> From<Box<T>> for Intern32<T> {
    fn from(val: Box<T>) -> Self {
        create_intern!(T, &*val, val)
    }
}

#[test]
fn test_intern_unsized() {
    let v: Intern32<str> = "hello".into();
    assert_eq!(&*v, "hello");
    assert_eq!(v, "hello".into());
    let v: Intern32<[u8]> = b"hello".into();
    assert_eq!(&*v, b"hello");
    assert_eq!(v, b"hello".into());
    let hello_slice: &[u8] = b"hello";
    let boxed_hello: Box<[u8]> = Box::from(hello_slice);
    assert_eq!(v, boxed_hello.into());

    let goodbye_slice: &[u8] = b"goodbye";
    let boxed_goodbye: Box<[u8]> = Box::from(goodbye_slice);
    assert!(v != boxed_goodbye.into());

    let v: Intern32<[usize]> = (&[0usize, 1, 2, 3]).into();
    assert_eq!(&*v, &[0, 1, 2, 3]);
    assert_eq!(v, (&[0usize, 1, 2, 3]).into());
}

impl<T: Eq + Hash + Send + Sync + 'static> Intern32<T> {
    /// Intern a value.
    ///
    /// If this value has not previously been interned, then `new` will allocate
    /// a spot for the value on the heap.  Otherwise, it will return a pointer
    /// to the object previously allocated.
    ///
    /// Note that `Intern32::new` is a bit slow, since it needs to check a
    /// `HashMap` protected by a `Mutex`.
    #[inline]
    pub fn new(val: T) -> Intern32<T> {
        create_intern!(T, &val, Box::new(val))
    }
    /// Intern a value from a reference.
    ///
    /// If this value has not previously been interned, then `new` will allocate
    /// a spot for the value on the heap and generate that value using
    /// `T::from(val)`.
    pub fn from_ref<'a, Q: ?Sized + Eq + Hash + 'a>(val: &'a Q) -> Intern32<T>
    where
        T: Borrow<Q> + From<&'a Q>,
    {
        create_intern!(T, val, Box::from(T::from(val)))
    }
}
impl<'a, Q, T> From<&'a Q> for Intern32<T>
where
    Q: Eq + Hash,
    T: Eq + Hash + Send + Sync + 'static + Borrow<Q>,
    Box<T>: From<&'a Q>,
{
    #[inline]
    fn from(value: &'a Q) -> Self {
        create_intern!(T, value, Box::from(value))
    }
}
impl<T: Eq + Hash + Send + Sync + 'static + ?Sized> Intern32<T> {
    /// Get a long-lived reference to the data pointed to by an `Intern`, which
    /// is never freed from the intern pool.
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn as_ref(self) -> &'static T {
        self.get_my_ref()
    }
    /// See how many objects have been interned.  This may be helpful
    /// in analyzing memory use.
    pub fn num_objects_interned() -> usize {
        INTERN_CONTAINERS.with(|m: &mut HashMap<&'static T, NonZeroU32>| -> usize { m.len() })
    }

    /// Only for benchmarking, this will cause problems
    ///
    /// Note that this does *not* clear out the existing stored values.
    #[cfg(feature = "bench")]
    pub fn benchmarking_only_clear_interns() {
        INTERN_CONTAINERS.with(|m: &mut HashMap<&'static T, NonZeroU32>| m.clear())
    }
    /// Check if a value already is interned.
    ///
    /// If this value has previously been interned, return true, else returns false
    ///
    /// ```rust
    ///
    /// use internment::Intern32;
    ///
    /// assert!(!Intern32::<String>::is_interned("Fortunato"));
    /// let x = Intern32::new("Fortunato".to_string());
    /// assert!(Intern32::<String>::is_interned("Fortunato"));
    ///
    /// assert!(!Intern32::<str>::is_interned("Fortunato"));
    /// let x: Intern32<str> = "Fortunato".into();
    /// assert!(Intern32::<str>::is_interned("Fortunato"));
    /// ```
    pub fn is_interned<'a, Q: ?Sized + Eq + Hash + 'a>(val: &'a Q) -> bool
    where
        T: Borrow<Q>,
    {
        INTERN_CONTAINERS
            .with(|m: &mut HashMap<&'static T, NonZeroU32>| -> bool { m.get(val).is_some() })
    }
}

#[cfg(feature = "bench")]
#[test]
fn test_benchmarking_only_clear_interns() {
    Intern32::<str>::benchmarking_only_clear_interns();
    assert_eq!(0, Intern32::<str>::num_objects_interned());
}

#[cfg(all(test, feature = "tinyset"))]
const fn sz<T>() -> u64 {
    core::mem::align_of::<T>() as u64
}
/// The `Fits64` implementation for `Intern<T>` is designed to normally give
/// (relatively) small numbers, by XORing with a fixed pointer that is also on
/// the heap.  The pointer is also divided by its alignment to eliminate those
/// redundant insignificant zeros.  This should make the most significant bits
/// of the resulting u64 be zero, which will mean that `Set64` (which is
/// space-efficient in storing small integers) can store this result in far
/// fewer than 8 bytes.
#[cfg_attr(docsrs, doc(cfg(feature = "tinyset")))]
#[cfg(feature = "tinyset")]
impl<T: Debug + Sync + Send> Fits64 for Intern32<T> {
    unsafe fn from_u64(x: u64) -> Self {
        Intern32 {
            index: NonZeroU32::new(x as u32 + 1).unwrap(),
            _phantom: std::marker::PhantomData,
        }
    }
    fn to_u64(self) -> u64 {
        u32::from(self.index) as u64 - 1
    }
}
#[test]
#[cfg(feature = "tinyset")]
fn test_intern_set64() {
    assert_eq!(1, sz::<u8>());
    assert_eq!(4, sz::<u32>());
    use tinyset::Set64;
    let mut s = Set64::<Intern32<u32>>::new();
    s.insert(Intern32::new(5));
    s.insert(Intern32::new(6));
    s.insert(Intern32::new(6));
    s.insert(Intern32::new(7));
    assert!(s.contains(Intern32::new(5)));
    assert!(s.contains(Intern32::new(6)));
    assert!(s.contains(Intern32::new(7)));
    assert!(!s.contains(Intern32::new(8)));
    for x in s.iter() {
        assert!([5, 6, 7, 8].contains(&x));
    }
    assert_eq!(s.len(), 3);
}

impl<T: ?Sized + Send + Sync> Intern32<T> {
    #[inline(always)]
    fn get_my_ref(self) -> &'static T {
        &*INTERN_DATA.get::<AppendOnlyVec<Box<T>>>()[u32::from(self.index) as usize - 1]
    }
}
impl<T: ?Sized + Send + Sync> AsRef<T> for Intern32<T> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        self.get_my_ref()
    }
}

#[cfg_attr(not(feature = "std"), allow(unused_macros))]
macro_rules! impl_as_ref {
    ($from:ty => $to:ty) => {
        impl AsRef<$to> for Intern32<$from> {
            #[inline(always)]
            fn as_ref(&self) -> &$to {
                self.get_my_ref().as_ref()
            }
        }
    };
}

#[cfg(feature = "std")]
impl_as_ref!(str => OsStr);
#[cfg(feature = "std")]
impl_as_ref!(str => Path);
#[cfg(feature = "std")]
impl_as_ref!(OsStr => Path);
#[cfg(feature = "std")]
impl_as_ref!(Path => OsStr);

impl<T: Eq + Hash + Send + Sync + ?Sized> Deref for Intern32<T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<T: Eq + Hash + Send + Sync + Display + ?Sized> Display for Intern32<T> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
        self.deref().fmt(f)
    }
}

impl<T: Eq + Hash + Send + Sync + ?Sized> Pointer for Intern32<T> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
        Pointer::fmt(&self.get_pointer(), f)
    }
}

/// The hash implementation returns the hash of the pointer
/// value, not the hash of the value pointed to.  This should
/// be irrelevant, since there is a unique pointer for every
/// value, but it *is* observable, since you could compare the
/// hash of the pointer with hash of the data itself.
impl<T: Eq + Hash + Send + Sync + ?Sized> Hash for Intern32<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_pointer().hash(state);
    }
}

impl<T: Eq + Hash + Send + Sync + ?Sized> PartialEq for Intern32<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        core::ptr::eq(self.get_pointer(), other.get_pointer())
    }
}
impl<T: Eq + Hash + Send + Sync + ?Sized> Eq for Intern32<T> {}

impl<T: Eq + Hash + Send + Sync + PartialOrd + ?Sized> PartialOrd for Intern32<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.as_ref().partial_cmp(other)
    }
    #[inline]
    fn lt(&self, other: &Self) -> bool {
        self.as_ref().lt(other)
    }
    #[inline]
    fn le(&self, other: &Self) -> bool {
        self.as_ref().le(other)
    }
    #[inline]
    fn gt(&self, other: &Self) -> bool {
        self.as_ref().gt(other)
    }
    #[inline]
    fn ge(&self, other: &Self) -> bool {
        self.as_ref().ge(other)
    }
}
impl<T: Eq + Hash + Send + Sync + Ord + ?Sized> Ord for Intern32<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_ref().cmp(other)
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
#[cfg(feature = "serde")]
impl<T: Eq + Hash + Send + Sync + Serialize + ?Sized> Serialize for Intern32<T> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_ref().serialize(serializer)
    }
}

impl<T: Eq + Hash + Send + Sync + Default + 'static> Default for Intern32<T> {
    #[inline]
    fn default() -> Self {
        Intern32::new(Default::default())
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
#[cfg(feature = "serde")]
impl<'de, T: Eq + Hash + Send + Sync + 'static + Deserialize<'de>> Deserialize<'de>
    for Intern32<T>
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        T::deserialize(deserializer).map(|x: T| Self::new(x))
    }
}

#[cfg(test)]
mod intern_tests {
    use super::Intern32;
    use alloc::{
        string::{String, ToString},
        vec,
    };
    use core::{borrow::Borrow, hash::Hash, ops::Deref};
    use std::println;

    #[cfg(feature = "deepsize")]
    use {
        super::{Box, HashMap, NonZeroU32, INTERN_CONTAINERS},
        alloc::sync::Arc,
        deepsize::{Context, DeepSizeOf},
    };

    #[test]
    fn eq_string() {
        assert_eq!(Intern32::new("hello"), Intern32::new("hello"));
        assert_ne!(Intern32::new("goodbye"), Intern32::new("farewell"));
    }
    #[test]
    fn display() {
        let world = Intern32::new("world");
        println!("Hello {}", world);
    }
    #[test]
    fn debug() {
        let world = Intern32::new("world");
        println!("Hello {:?}", world);
    }
    #[test]
    fn has_default() {
        assert_eq!(
            Intern32::<Option<String>>::default(),
            Intern32::<Option<String>>::new(None)
        );
    }
    #[test]
    fn can_clone() {
        assert_eq!(
            Intern32::<Option<String>>::default().clone(),
            Intern32::<Option<String>>::new(None)
        );
    }
    #[test]
    fn can_clone_str() {
        let x: Intern32<str> = From::from("hello");
        assert_eq!(x, x.clone());
    }
    #[test]
    fn has_borrow() {
        let x = Intern32::<Option<String>>::default();
        let b: &Option<String> = x.borrow();
        assert_eq!(b, Intern32::<Option<String>>::new(None).as_ref());
    }
    #[test]
    fn has_deref() {
        let x = Intern32::<Option<String>>::default();
        let b: &Option<String> = x.as_ref();
        assert_eq!(b, Intern32::<Option<String>>::new(None).deref());
    }

    #[cfg(test)]
    #[derive(Eq, PartialEq, Hash)]
    pub struct TestStruct(String, u64);

    // Quickly create a small number of interned objects from
    // multiple threads.
    #[test]
    fn multithreading_intern() {
        use std::thread;
        let mut thandles = vec![];
        for _i in 0..10 {
            thandles.push(thread::spawn(|| {
                for _i in 0..100_000 {
                    let _interned1 = Intern32::new(TestStruct("foo".to_string(), 5));
                    let _interned2 = Intern32::new(TestStruct("bar".to_string(), 10));
                }
            }));
        }
        for h in thandles.into_iter() {
            h.join().unwrap()
        }
    }
    // Quickly create a small number of interned objects from
    // multiple threads.  This test is faster to run under miri.
    #[test]
    fn multithreading_normal_intern() {
        use std::thread;
        let mut thandles = vec![];
        for _i in 0..10 {
            thandles.push(thread::spawn(|| {
                for _i in 0..100 {
                    let _interned1 = Intern32::new(TestStruct("normalfoo".to_string(), 5));
                    let _interned2 = Intern32::new(TestStruct("normalbar".to_string(), 10));
                }
            }));
        }
        for h in thandles.into_iter() {
            h.join().unwrap()
        }
    }

    #[cfg(feature = "deepsize")]
    #[test]
    fn test_deep_size() {
        let string1 = String::from("abcdefghijklmnopqrstuvwxyz");
        let string2 = string1.clone();
        let string3 = string1.clone();
        // 3 string are the same, interned only once
        let _ = Intern32::new(string1.clone());
        let _ = Intern32::new(string2);
        let _ = Intern32::new(string3);
        // size of set
        let set_size = {
            use deepsize::DeepSizeOf;
            let mut set: HashMap<&'static String, u32> = HashMap::new();
            set.insert(Box::leak(Box::new(string1.clone())), 0_u32);
            set.deep_size_of()
        };
        // size of the data
        let data_size = 16 + (&string1).deep_size_of();

        let interned_size = Intern32::<String>::deep_size_of_interned();
        println!("data_size: {data_size}, set_size: {set_size}");
        assert_eq!(interned_size, set_size + data_size);
    }

    #[cfg(feature = "deepsize")]
    #[derive(Clone)]
    struct ArcInside {
        hash: usize,
        pointer: Arc<String>,
    }

    #[cfg(feature = "deepsize")]
    impl Hash for ArcInside {
        /// For testing purposes, we only hash the hash field.
        /// In order to make [`ArcInside`] instances containing the same string have different hash values.
        fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
            self.hash.hash(state);
        }
    }

    #[cfg(feature = "deepsize")]
    impl PartialEq for ArcInside {
        /// For testing purposes, we only compare the hash field.
        fn eq(&self, other: &Self) -> bool {
            self.hash == other.hash
        }
    }

    #[cfg(feature = "deepsize")]
    impl Eq for ArcInside {}

    #[cfg(feature = "deepsize")]
    impl DeepSizeOf for ArcInside {
        fn deep_size_of_children(&self, context: &mut Context) -> usize {
            self.pointer.deep_size_of_children(context)
        }
    }

    #[cfg(feature = "deepsize")]
    #[test]
    fn test_deep_size_with_context() {
        let string = String::from("abcdefghijklmnopqrstuvwxyz");
        // size of string inside arc, 50 bytes.
        // Three arcs pointed to the same string will not be counted multiple times.
        let string_size = string.deep_size_of();

        let a1 = ArcInside {
            hash: 1,
            pointer: Arc::new(string),
        };
        let a2 = ArcInside {
            hash: 2,
            pointer: a1.pointer.clone(),
        };
        let a3 = ArcInside {
            hash: 3,
            pointer: a1.pointer.clone(),
        };
        // size of ArcInside, 16 bytes each
        let object_size = core::mem::size_of::<ArcInside>() * 3;

        let _ = Intern32::new(a1);
        let _ = Intern32::new(a2);
        let _ = Intern32::new(a3);

        // size of map
        let map_size = {
            use deepsize::DeepSizeOf;
            let mut map: HashMap<&'static String, u32> = HashMap::new();
            // The precise values don't matter since the HashMap DeepSizeOf
            // impelementation doesn't take into account the sizes of keys.
            map.insert(Box::leak(Box::new("1".to_string())), 0_u32);
            map.insert(Box::leak(Box::new("2".to_string())), 1_u32);
            map.insert(Box::leak(Box::new("3".to_string())), 2_u32);
            map.deep_size_of()
        };

        let interned_size = Intern32::<ArcInside>::deep_size_of_interned();

        println!("string_size: {}", string_size);
        println!("object_size: {}", object_size);
        println!("map_size: {map_size}");
        println!("interned_size: {}", interned_size);

        // 3 ArcInside has different hash values
        INTERN_CONTAINERS
            .with(|m: &mut HashMap<&'static ArcInside, NonZeroU32>| assert_eq!(m.len(), 3));

        assert_eq!(interned_size, 8 + string_size + object_size + map_size);
    }
}

impl<T: Debug + ?Sized + Send + Sync> Debug for Intern32<T> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
        self.as_ref().fmt(f)
    }
}

#[test]
fn test_intern_num_objects() {
    assert_eq!(Intern32::<i32>::num_objects_interned(), 0);
    assert_eq!(Intern32::new(5), Intern32::new(5));
    {
        let interned = Intern32::new(6);
        assert_eq!(*interned, 6);
        assert_eq!(Intern32::<i32>::num_objects_interned(), 2);
    }
    {
        let _interned = Intern32::new(6);
        assert_eq!(Intern32::<i32>::num_objects_interned(), 2);
    }
    {
        let _interned = Intern32::new(7);
        assert_eq!(Intern32::<i32>::num_objects_interned(), 3);
    }
}
