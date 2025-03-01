#![deny(missing_docs)]
use super::{boxedset, container};
use alloc::boxed::Box;
use boxedset::HashSet;
use core::{
    borrow::Borrow,
    convert::AsRef,
    fmt::{Debug, Display, Pointer},
    hash::{Hash, Hasher},
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
/// A pointer to an interned object.
///
/// The interned object will be held in memory indefinitely.  On the
/// plus side, this means that lifetime issues are simple when using
/// `Intern`.
///
/// # Example
/// ```rust
/// use internment::Intern;
///
/// let x = Intern::new("hello");
/// let y = Intern::new("world");
/// assert_ne!(x, y);
/// assert_eq!(x, Intern::new("hello"));
/// assert_eq!(*x, "hello"); // dereference an Intern like a pointer
/// ```
///
/// # Example with owned `String` data
///
/// ```rust
/// use internment::Intern;
///
/// let x = Intern::new("hello".to_string());
/// let y = Intern::<String>::from_ref("world");
/// assert_ne!(x, y);
/// assert_eq!(x, Intern::from_ref("hello"));
/// assert_eq!(y, Intern::from_ref("world"));
/// assert_eq!(&*x, "hello"); // dereference a Intern like a pointer
/// ```
pub struct Intern<T: 'static + ?Sized> {
    pointer: &'static T,
}

#[test]
fn like_doctest_intern() {
    let x = Intern::new("hello".to_string());
    let y = Intern::<String>::from_ref("world");
    assert_ne!(x, y);
    assert_eq!(x, Intern::from_ref("hello"));
    assert_eq!(y, Intern::from_ref("world"));
    assert_eq!(&*x, "hello"); // dereference a Intern like a pointer\
    let _ = Intern::<String>::from_ref("Fortunato");
    assert!(Intern::<String>::is_interned("Fortunato"));
    assert!(!Intern::<String>::is_interned("Montresor"));
}

#[cfg(feature = "deepsize")]
impl<T: 'static + ?Sized> deepsize::DeepSizeOf for Intern<T> {
    fn deep_size_of_children(&self, _context: &mut deepsize::Context) -> usize {
        0
    }
}

#[cfg_attr(docsrs, doc(cfg(all(feature = "deepsize", feature = "intern"))))]
/// Return the memory used by all interned objects of the given type.
#[cfg(feature = "deepsize")]
pub fn deep_size_of_interned<T: Eq + Hash + Send + Sync + 'static + deepsize::DeepSizeOf>() -> usize
{
    use deepsize::DeepSizeOf;
    INTERN_CONTAINERS.with(|m: &mut HashSet<&'static T>| -> usize { (*m).deep_size_of() })
}

#[test]
fn has_niche() {
    assert_eq!(
        core::mem::size_of::<Intern<String>>(),
        core::mem::size_of::<usize>(),
    );
    assert_eq!(
        core::mem::size_of::<Option<Intern<String>>>(),
        core::mem::size_of::<usize>(),
    );
}

impl<T: ?Sized> Clone for Intern<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

/// An `Intern` is `Copy`, which is unusual for a pointer.  This is safe
/// because we never free the data pointed to by an `Intern`.
impl<T: ?Sized> Copy for Intern<T> {}

impl<T: ?Sized> Intern<T> {
    #[inline(always)]
    fn get_pointer(&self) -> *const T {
        self.pointer as *const T
    }
}

static INTERN_CONTAINERS: container::Arena = container::Arena::new();

macro_rules! from_via_box {
    ($t:ty) => {
        impl From<&$t> for Intern<$t> {
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
impl<T: Eq + Hash + Send + Sync + 'static + Copy> From<&[T]> for Intern<[T]> {
    #[inline]
    fn from(val: &[T]) -> Self {
        Self::via_box(val)
    }
}

impl<T: Eq + Hash + Send + Sync + 'static + Copy, const N: usize> From<&[T; N]> for Intern<[T]> {
    /// Converts a `[T; N]` into a `Intern<[T]>`
    #[inline]
    fn from(val: &[T; N]) -> Self {
        Self::via_box(val)
    }
}

impl<T: Eq + Hash + Send + Sync + 'static + ?Sized> Intern<T> {
    /// This method to be used internally
    fn via_box<'a, I>(val: &'a I) -> Self
    where
        Box<T>: From<&'a I>,
        I: Borrow<T> + ?Sized,
    {
        INTERN_CONTAINERS.with(|m: &mut HashSet<&'static T>| -> Self {
            if let Some(&b) = m.get(val.borrow()) {
                return Intern { pointer: b };
            }
            let p: &'static T = Box::leak(Box::from(val));
            m.insert(p);
            Intern { pointer: p }
        })
    }
}

impl<T: Eq + Hash + Send + Sync + 'static + ?Sized> From<Box<T>> for Intern<T> {
    fn from(val: Box<T>) -> Self {
        INTERN_CONTAINERS.with(|m: &mut HashSet<&'static T>| -> Self {
            if let Some(&b) = m.get(val.borrow()) {
                return Intern { pointer: b };
            }
            let p: &'static T = Box::leak(val);
            m.insert(p);
            Intern { pointer: p }
        })
    }
}

#[test]
fn test_intern_unsized() {
    let v: Intern<str> = "hello".into();
    assert_eq!(&*v, "hello");
    assert_eq!(v, "hello".into());
    let v: Intern<[u8]> = b"hello".into();
    assert_eq!(&*v, b"hello");
    assert_eq!(v, b"hello".into());
    let hello_slice: &[u8] = b"hello";
    let boxed_hello: Box<[u8]> = Box::from(hello_slice);
    assert_eq!(v, boxed_hello.into());

    let goodbye_slice: &[u8] = b"goodbye";
    let boxed_goodbye: Box<[u8]> = Box::from(goodbye_slice);
    assert!(v != boxed_goodbye.into());

    let v: Intern<[usize]> = (&[0usize, 1, 2, 3]).into();
    assert_eq!(&*v, &[0, 1, 2, 3]);
    assert_eq!(v, (&[0usize, 1, 2, 3]).into());
}

impl<T: Eq + Hash + Send + Sync + 'static> Intern<T> {
    /// Intern a value.
    ///
    /// If this value has not previously been interned, then `new` will allocate
    /// a spot for the value on the heap.  Otherwise, it will return a pointer
    /// to the object previously allocated.
    ///
    /// Note that `Intern::new` is a bit slow, since it needs to check a
    /// `HashSet` protected by a `Mutex`.
    pub fn new(val: T) -> Intern<T> {
        INTERN_CONTAINERS.with(|m: &mut HashSet<&'static T>| -> Intern<T> {
            if let Some(&b) = m.get(&val) {
                return Intern { pointer: b };
            }
            let p: &'static T = Box::leak(Box::new(val));
            m.insert(p);
            Intern { pointer: p }
        })
    }
    /// Intern a value from a reference.
    ///
    /// If this value has not previously been interned, then `new` will allocate
    /// a spot for the value on the heap and generate that value using
    /// `T::from(val)`.
    pub fn from_ref<'a, Q: ?Sized + Eq + Hash + 'a>(val: &'a Q) -> Intern<T>
    where
        T: Borrow<Q> + From<&'a Q>,
    {
        INTERN_CONTAINERS.with(|m: &mut HashSet<&'static T>| -> Intern<T> {
            if let Some(&b) = m.get(val) {
                return Intern { pointer: b };
            }
            let p = Box::leak(Box::new(T::from(val)));
            m.insert(p);
            Intern { pointer: p }
        })
    }
}
impl<T: Eq + Hash + Send + Sync + 'static + ?Sized> Intern<T> {
    /// Get a long-lived reference to the data pointed to by an `Intern`, which
    /// is never freed from the intern pool.
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn as_ref(self) -> &'static T {
        self.pointer
    }
    /// See how many objects have been interned.  This may be helpful
    /// in analyzing memory use.
    pub fn num_objects_interned() -> usize {
        INTERN_CONTAINERS.with(|m: &mut HashSet<&'static T>| -> usize { m.len() })
    }

    /// Only for benchmarking, this will cause problems
    #[cfg(feature = "bench")]
    pub fn benchmarking_only_clear_interns() {
        INTERN_CONTAINERS.with(|m: &mut HashSet<&'static T>| m.clear())
    }
    /// Check if a value already is interned.
    ///
    /// If this value has previously been interned, return true, else returns false/// Checking if an object is already interned
    ///
    /// ```rust
    ///
    /// use internment::Intern;
    ///
    /// assert!(!Intern::<String>::is_interned("Fortunato"));
    /// let x = Intern::new("Fortunato".to_string());
    /// assert!(Intern::<String>::is_interned("Fortunato"));
    ///
    /// assert!(!Intern::<str>::is_interned("Fortunato"));
    /// let x: Intern<str> = "Fortunato".into();
    /// assert!(Intern::<str>::is_interned("Fortunato"));
    /// ```
    pub fn is_interned<'a, Q: ?Sized + Eq + Hash + 'a>(val: &'a Q) -> bool
    where
        T: Borrow<Q>,
    {
        INTERN_CONTAINERS.with(|m: &mut HashSet<&'static T>| -> bool { m.get(val).is_some() })
    }
}

#[cfg(feature = "bench")]
#[test]
fn test_benchmarking_only_clear_interns() {
    Intern::<str>::benchmarking_only_clear_interns();
    assert_eq!(0, Intern::<str>::num_objects_interned());
}

#[cfg(feature = "tinyset")]
#[cold]
fn allocate_ptr() -> *mut usize {
    let aref: &usize = Box::leak(Box::new(0));
    aref as *const usize as *mut usize
}

#[cfg(feature = "tinyset")]
fn heap_location() -> u64 {
    static HEAP_LOCATION: core::sync::atomic::AtomicPtr<usize> =
        core::sync::atomic::AtomicPtr::new(0 as *mut usize);
    let mut p = HEAP_LOCATION.load(core::sync::atomic::Ordering::Relaxed) as u64;
    if p == 0 {
        let ptr = allocate_ptr();
        p = match HEAP_LOCATION.compare_exchange(
            core::ptr::null_mut(),
            ptr,
            core::sync::atomic::Ordering::Relaxed,
            core::sync::atomic::Ordering::Relaxed,
        ) {
            Ok(_) => ptr as u64,
            Err(ptr) => ptr as u64, // this means another thread allocated this.
        };
    }
    p
}
#[cfg(feature = "tinyset")]
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
impl<T: Debug> Fits64 for Intern<T> {
    unsafe fn from_u64(x: u64) -> Self {
        Intern {
            pointer: &*(((x ^ (heap_location() / sz::<T>())) * sz::<T>()) as *const T),
        }
    }
    fn to_u64(self) -> u64 {
        (self.get_pointer() as u64 / sz::<T>()) ^ (heap_location() / sz::<T>())
    }
}
#[test]
#[cfg(feature = "tinyset")]
fn test_intern_set64() {
    assert_eq!(1, sz::<u8>());
    assert_eq!(4, sz::<u32>());
    use tinyset::Set64;
    let mut s = Set64::<Intern<u32>>::new();
    s.insert(Intern::new(5));
    s.insert(Intern::new(6));
    s.insert(Intern::new(6));
    s.insert(Intern::new(7));
    assert!(s.contains(Intern::new(5)));
    assert!(s.contains(Intern::new(6)));
    assert!(s.contains(Intern::new(7)));
    assert!(!s.contains(Intern::new(8)));
    for x in s.iter() {
        assert!([5, 6, 7, 8].contains(&x));
    }
    assert_eq!(s.len(), 3);
}

impl<T: ?Sized> AsRef<T> for Intern<T> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        self.pointer
    }
}

#[cfg_attr(not(feature = "std"), allow(unused_macros))]
macro_rules! impl_as_ref {
    ($from:ty => $to:ty) => {
        impl AsRef<$to> for Intern<$from> {
            #[inline(always)]
            fn as_ref(&self) -> &$to {
                self.pointer.as_ref()
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

impl<T: Eq + Hash + Send + Sync + ?Sized> Deref for Intern<T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<T: Eq + Hash + Send + Sync + Display + ?Sized> Display for Intern<T> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
        self.deref().fmt(f)
    }
}

impl<T: Eq + Hash + Send + Sync + ?Sized> Pointer for Intern<T> {
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
impl<T: Eq + Hash + Send + Sync + ?Sized> Hash for Intern<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_pointer().hash(state);
    }
}

impl<T: Eq + Hash + Send + Sync + ?Sized> PartialEq for Intern<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        core::ptr::eq(self.get_pointer(), other.get_pointer())
    }
}
impl<T: Eq + Hash + Send + Sync + ?Sized> Eq for Intern<T> {}

impl<T: Eq + Hash + Send + Sync + PartialOrd + ?Sized> PartialOrd for Intern<T> {
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
impl<T: Eq + Hash + Send + Sync + Ord + ?Sized> Ord for Intern<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_ref().cmp(other)
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
#[cfg(feature = "serde")]
impl<T: Eq + Hash + Send + Sync + Serialize + ?Sized> Serialize for Intern<T> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_ref().serialize(serializer)
    }
}

impl<T: Eq + Hash + Send + Sync + 'static> From<T> for Intern<T> {
    #[inline]
    fn from(t: T) -> Self {
        Intern::new(t)
    }
}
impl<T: Eq + Hash + Send + Sync + Default + 'static> Default for Intern<T> {
    #[inline]
    fn default() -> Self {
        Intern::new(Default::default())
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
#[cfg(feature = "serde")]
impl<'de, T: Eq + Hash + Send + Sync + 'static + Deserialize<'de>> Deserialize<'de> for Intern<T> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        T::deserialize(deserializer).map(|x: T| Self::new(x))
    }
}

#[cfg(test)]
mod intern_tests {
    use super::Intern;
    use alloc::{
        string::{String, ToString},
        vec,
    };
    use core::{borrow::Borrow, hash::Hash, ops::Deref};
    use std::println;

    #[cfg(feature = "deepsize")]
    use {
        super::INTERN_CONTAINERS,
        crate::{boxedset::HashSet, deep_size_of_interned},
        alloc::sync::Arc,
        deepsize::{Context, DeepSizeOf},
    };

    #[test]
    fn eq_string() {
        assert_eq!(Intern::new("hello"), Intern::new("hello"));
        assert_ne!(Intern::new("goodbye"), Intern::new("farewell"));
    }
    #[test]
    fn display() {
        let world = Intern::new("world");
        println!("Hello {}", world);
    }
    #[test]
    fn debug() {
        let world = Intern::new("world");
        println!("Hello {:?}", world);
    }
    #[test]
    fn has_default() {
        assert_eq!(
            Intern::<Option<String>>::default(),
            Intern::<Option<String>>::new(None)
        );
    }
    #[test]
    fn can_clone() {
        assert_eq!(
            Intern::<Option<String>>::default().clone(),
            Intern::<Option<String>>::new(None)
        );
    }
    #[test]
    fn can_clone_str() {
        let x: Intern<str> = From::from("hello");
        assert_eq!(x, x.clone());
    }
    #[test]
    fn has_borrow() {
        let x = Intern::<Option<String>>::default();
        let b: &Option<String> = x.borrow();
        assert_eq!(b, Intern::<Option<String>>::new(None).as_ref());
    }
    #[test]
    fn has_deref() {
        let x = Intern::<Option<String>>::default();
        let b: &Option<String> = x.as_ref();
        assert_eq!(b, Intern::<Option<String>>::new(None).deref());
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
                    let _interned1 = Intern::new(TestStruct("foo".to_string(), 5));
                    let _interned2 = Intern::new(TestStruct("bar".to_string(), 10));
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
                    let _interned1 = Intern::new(TestStruct("normalfoo".to_string(), 5));
                    let _interned2 = Intern::new(TestStruct("normalbar".to_string(), 10));
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
        let string_size = string1.deep_size_of();

        let _ = Intern::new(string1);
        let _ = Intern::new(string2);
        let _ = Intern::new(string3);
        // size of set
        let set_size =
            INTERN_CONTAINERS.with(|m: &mut HashSet<&'static String>| core::mem::size_of_val(m));
        // size of pointers in the set
        let pointers_in_set_size = INTERN_CONTAINERS.with(|m: &mut HashSet<&'static String>| {
            core::mem::size_of::<&'static String>() * m.capacity()
        });

        let interned_size = deep_size_of_interned::<String>();
        assert_eq!(interned_size, string_size + set_size + pointers_in_set_size);
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

        let _ = Intern::new(a1);
        let _ = Intern::new(a2);
        let _ = Intern::new(a3);

        // size of set
        let set_size =
            INTERN_CONTAINERS.with(|m: &mut HashSet<&'static ArcInside>| core::mem::size_of_val(m));
        // size of pointers in the set
        let pointers_in_set_size = INTERN_CONTAINERS.with(|m: &mut HashSet<&'static ArcInside>| {
            core::mem::size_of::<&'static ArcInside>() * m.capacity()
        });

        let interned_size = deep_size_of_interned::<ArcInside>();

        println!("string_size: {}", string_size);
        println!("object_size: {}", object_size);
        println!("set_size: {}", set_size);
        println!("pointers_in_set_size: {}", pointers_in_set_size);
        println!("interned_size: {}", interned_size);

        // 3 ArcInside has different hash values
        INTERN_CONTAINERS.with(|m: &mut HashSet<&'static ArcInside>| assert_eq!(m.len(), 3));

        assert_eq!(
            interned_size,
            string_size + object_size + set_size + pointers_in_set_size
        );
    }
}

impl<T: Debug + ?Sized> Debug for Intern<T> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
        self.as_ref().fmt(f)
    }
}

#[test]
fn test_intern_num_objects() {
    assert_eq!(Intern::<i32>::num_objects_interned(), 0);
    assert_eq!(Intern::new(5), Intern::new(5));
    {
        let interned = Intern::new(6);
        assert_eq!(*interned, 6);
        assert_eq!(Intern::<i32>::num_objects_interned(), 2);
    }
    {
        let _interned = Intern::new(6);
        assert_eq!(Intern::<i32>::num_objects_interned(), 2);
    }
    {
        let _interned = Intern::new(7);
        assert_eq!(Intern::<i32>::num_objects_interned(), 3);
    }
}
