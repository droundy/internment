#![deny(missing_docs)]
use std::any::Any;
use std::any::TypeId;
use std::hash::{Hash, Hasher};

use append_only_vec::AppendOnlyVec;

struct AnySend(Box<dyn Any + Send + Sync>);

const CONTAINER_COUNT: usize = 32;
const EMPTY: AppendOnlyVec<AnySend> = AppendOnlyVec::new();
static CONTAINERS: [AppendOnlyVec<AnySend>; CONTAINER_COUNT] = [EMPTY; CONTAINER_COUNT];

pub fn with_mutex_hashset<F, T, R>(f: F) -> R
where
    F: FnOnce(&mut HashSet<T>) -> R,
    T: Any + Send + Sync,
{
    // Compute the hash of the type.
    fn hash_of_type<T: 'static>() -> usize {
        // We use very simple hasher, because it is optimized away to a constant:
        // https://rust.godbolt.org/z/4T1fa4GGs
        // which is not true for using `DefaultHasher`:
        // https://rust.godbolt.org/z/qKar1WKfz
        struct HasherForTypeId {
            hash: u64,
        }

        impl Hasher for HasherForTypeId {
            fn write(&mut self, bytes: &[u8]) {
                // Hash for type only calls `write_u64` once,
                // but handle this case explicitly to make sure
                // this code doesn't break if stdlib internals change.

                for byte in bytes {
                    self.hash = self.hash.wrapping_mul(31).wrapping_add(*byte as u64);
                }
            }

            fn write_u64(&mut self, v: u64) {
                self.hash = v;
            }

            fn finish(&self) -> u64 {
                self.hash
            }
        }

        let mut hasher = HasherForTypeId { hash: 0 };
        TypeId::of::<Mutex<HashSet<T>>>().hash(&mut hasher);
        hasher.hash as usize
    }

    use core::ops::DerefMut;
    for v in CONTAINERS[hash_of_type::<T>() % CONTAINER_COUNT].iter() {
        if let Some(m) = v.0.downcast_ref::<Mutex<HashSet<T>>>() {
            let mut m = m.lock();
            return f(m.deref_mut());
        }
    }
    let default: Mutex<HashSet<T>> = Mutex::new(HashSet::new());
    CONTAINERS[hash_of_type::<T>() % CONTAINER_COUNT].push(AnySend(Box::new(default)));
    // We now search through the AppendOnlyVec, just in case there was a race
    // and two things of the same type got pushed sumultaneously.  If that
    // happens, we'll just use the first one.  It's a little hokey leaving this
    // race condition here, but at worst it should just slow down access to a
    // different type.
    for v in CONTAINERS[hash_of_type::<T>() % CONTAINER_COUNT].iter() {
        if let Some(m) = v.0.downcast_ref::<Mutex<HashSet<T>>>() {
            let mut m = m.lock();
            return f(m.deref_mut());
        }
    }
    unreachable!()
}

use super::boxedset;
use boxedset::HashSet;
use parking_lot::Mutex;
use std::borrow::Borrow;
use std::convert::AsRef;
use std::fmt::{Debug, Display, Pointer};
use std::ops::Deref;

#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};
#[cfg(feature = "tinyset")]
use tinyset::Fits64;

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
/// let y = Intern::<String>::from("world");
/// assert_ne!(x, y);
/// assert_eq!(x, Intern::from("hello"));
/// assert_eq!(y, Intern::from("world"));
/// assert_eq!(&*x, "hello"); // dereference a Intern like a pointer
/// ```

#[test]
fn like_doctest_intern() {
    let x = Intern::new("hello".to_string());
    let y = Intern::<String>::from("world");
    assert_ne!(x, y);
    assert_eq!(x, Intern::from("hello"));
    assert_eq!(y, Intern::from("world"));
    assert_eq!(&*x, "hello"); // dereference a Intern like a pointer\
}

#[cfg_attr(docsrs, doc(cfg(feature = "intern")))]
/// A pointer to an interned object
///
/// An `Intern` points to an object that has been leaked and may be used in any
/// thread without locking.
pub struct Intern<T: 'static + ?Sized> {
    pointer: &'static T,
}

#[test]
fn has_niche() {
    assert_eq!(
        std::mem::size_of::<Intern<String>>(),
        std::mem::size_of::<usize>(),
    );
    assert_eq!(
        std::mem::size_of::<Option<Intern<String>>>(),
        std::mem::size_of::<usize>(),
    );
}

impl<T: ?Sized> Clone for Intern<T> {
    fn clone(&self) -> Self {
        Intern {
            pointer: self.pointer,
        }
    }
}

/// An `Intern` is `Copy`, which is unusal for a pointer.  This is safe
/// because we never free the data pointed to by an `Intern`.
impl<T: ?Sized> Copy for Intern<T> {}

impl<T: ?Sized> Intern<T> {
    fn get_pointer(&self) -> *const T {
        self.pointer as *const T
    }
}

macro_rules! from_via_box {
    ($t:ty) => {
        impl From<&$t> for Intern<$t> {
            fn from(val: &$t) -> Self {
                Self::via_box(val)
            }
        }
    };
}
from_via_box!(std::ffi::CStr);
from_via_box!(str);
from_via_box!(std::path::Path);
impl<T: Eq + Hash + Send + Sync + 'static + Copy> From<&[T]> for Intern<[T]> {
    fn from(val: &[T]) -> Self {
        Self::via_box(val)
    }
}

impl<T: Eq + Hash + Send + Sync + 'static + Copy, const N: usize> From<&[T; N]> for Intern<[T]> {
    /// Converts a `[T; N]` into a `Intern<[T]>`
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
        with_mutex_hashset(|m: &mut HashSet<&'static T>| -> Self {
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
        with_mutex_hashset(|m: &mut HashSet<&'static T>| -> Self {
            if let Some(&b) = m.get(val.borrow()) {
                return Intern { pointer: b };
            }
            let p: &'static T = Box::leak(Box::from(val));
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
        with_mutex_hashset(|m: &mut HashSet<&'static T>| -> Intern<T> {
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
    /// If this value has not previously been
    /// interned, then `new` will allocate a spot for the value on the
    /// heap and generate that value using `T::from(val)`.
    pub fn from<'a, Q: ?Sized + Eq + Hash + 'a>(val: &'a Q) -> Intern<T>
    where
        T: Borrow<Q> + From<&'a Q>,
    {
        with_mutex_hashset(|m: &mut HashSet<&'static T>| -> Intern<T> {
            if let Some(&b) = m.get(val) {
                return Intern { pointer: b };
            }
            let p = Box::leak(Box::new(T::from(val)));
            m.insert(p);
            Intern { pointer: p }
        })
    }
}

impl<T: Any + Eq + Hash + Send + Sync + ?Sized> Intern<T> {
    /// Get a long-lived reference to the data pointed to by an `Intern`, which
    /// is never freed from the intern pool.
    pub fn as_ref(self) -> &'static T {
        self.pointer
    }
    /// See how many objects have been interned.  This may be helpful
    /// in analyzing memory use.
    pub fn num_objects_interned() -> usize {
        with_mutex_hashset(|m: &mut HashSet<&'static T>| -> usize { m.len() })
    }

    /// Only for benchmarking, this will cause problems
    #[cfg(feature = "bench")]
    pub fn benchmarking_only_clear_interns() {
        with_mutex_hashset(|m: &mut HashSet<&'static T>| -> () { m.clear() })
    }
}

#[cfg(feature = "tinyset")]
#[cold]
fn allocate_ptr() -> *mut usize {
    let aref: &usize = Box::leak(Box::new(0));
    aref as *const usize as *mut usize
}

#[cfg(feature = "tinyset")]
fn heap_location() -> u64 {
    static HEAP_LOCATION: std::sync::atomic::AtomicPtr<usize> =
        std::sync::atomic::AtomicPtr::new(0 as *mut usize);
    let mut p = HEAP_LOCATION.load(std::sync::atomic::Ordering::Relaxed) as u64;
    if p == 0 {
        let ptr = allocate_ptr();
        p = match HEAP_LOCATION.compare_exchange(
            std::ptr::null_mut(),
            ptr,
            std::sync::atomic::Ordering::Relaxed,
            std::sync::atomic::Ordering::Relaxed,
        ) {
            Ok(_) => ptr as u64,
            Err(ptr) => {
                println!("race, ptr is {:p}", ptr);
                ptr as u64
            }
        }
    }
    p
}
#[cfg(feature = "tinyset")]
const fn sz<T>() -> u64 {
    std::mem::align_of::<T>() as u64
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
            pointer: &*(((x ^ heap_location() / sz::<T>()) * sz::<T>()) as *const T),
        }
    }
    fn to_u64(self) -> u64 {
        self.get_pointer() as u64 / sz::<T>() ^ heap_location() / sz::<T>()
    }
}
#[test]
#[cfg(feature = "tinyset")]
fn test_intern_set64() {
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
    assert_eq!(s.len(), 3);
}

impl<T: ?Sized> AsRef<T> for Intern<T> {
    fn as_ref(&self) -> &T {
        self.pointer
    }
}

impl<T: Eq + Hash + Send + Sync + ?Sized> Deref for Intern<T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<T: Eq + Hash + Send + Sync + Display + ?Sized> Display for Intern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.deref().fmt(f)
    }
}

impl<T: Eq + Hash + Send + Sync + ?Sized> Pointer for Intern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        Pointer::fmt(&self.get_pointer(), f)
    }
}

/// The hash implementation returns the hash of the pointer
/// value, not the hash of the value pointed to.  This should
/// be irrelevant, since there is a unique pointer for every
/// value, but it *is* observable, since you could compare the
/// hash of the pointer with hash of the data itself.
impl<T: Eq + Hash + Send + Sync + ?Sized> Hash for Intern<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_pointer().hash(state);
    }
}

impl<T: Eq + Hash + Send + Sync + ?Sized> PartialEq for Intern<T> {
    fn eq(&self, other: &Self) -> bool {
        self.get_pointer() == other.get_pointer()
    }
}
impl<T: Eq + Hash + Send + Sync + ?Sized> Eq for Intern<T> {}

impl<T: Eq + Hash + Send + Sync + PartialOrd + ?Sized> PartialOrd for Intern<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_ref().partial_cmp(other)
    }
    fn lt(&self, other: &Self) -> bool {
        self.as_ref().lt(other)
    }
    fn le(&self, other: &Self) -> bool {
        self.as_ref().le(other)
    }
    fn gt(&self, other: &Self) -> bool {
        self.as_ref().gt(other)
    }
    fn ge(&self, other: &Self) -> bool {
        self.as_ref().ge(other)
    }
}
impl<T: Eq + Hash + Send + Sync + Ord + ?Sized> Ord for Intern<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_ref().cmp(other)
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
#[cfg(feature = "serde")]
impl<T: Eq + Hash + Send + Sync + Serialize> Serialize for Intern<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_ref().serialize(serializer)
    }
}

impl<T: Eq + Hash + Send + Sync + 'static> From<T> for Intern<T> {
    fn from(t: T) -> Self {
        Intern::new(t)
    }
}
impl<T: Eq + Hash + Send + Sync + Default + 'static> Default for Intern<T> {
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
    use super::{Borrow, Deref};
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
}

impl<T: Debug + ?Sized> Debug for Intern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        std::fmt::Debug::fmt(&self.get_pointer(), f)?;
        f.write_str(" : ")?;
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

#[cfg(test)]
#[derive(Eq, PartialEq, Hash)]
pub struct TestStructCount(String, u64, std::sync::Arc<bool>);

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
