// Copyright 2018,2020 David Roundy
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! A very easy to use library for
//! [interning](https://en.wikipedia.org/wiki/String_interning)
//! strings or other data in rust.  Interned data is very efficient to
//! either hash or compare for equality (just a pointer comparison).
//! Data is also automatically de-duplicated.
//!
//! You have two options with the internment crate:
//!
//! 1. `Intern`, which will never free your data.  This means that an
//! `Intern` is `Copy`, so you can make as many copies of the pointer
//! as you may care to at no cost.
//!
//! 2. `ArcIntern`, which reference-counts your data and frees it when
//! there are no more references.  `ArcIntern` will keep memory use
//! down, but uses an atomic increment/decrement whenever a clone of
//! your pointer is made, or a pointer is dropped.
//!
//! In each case, accessing your data is a single pointer dereference, and
//! the size of any internment data structure (`Intern` or
//! `ArcIntern`) is a single pointer.  In each case, you have a guarantee
//! that a single data value (as defined by `Eq` and `Hash`) will
//! correspond to a single pointer value.  This means that we can use
//! pointer comparison (and a pointer hash) in place of value comparisons,
//! which is very fast.
//!
//! # Example
//! ```rust
//! use internment::Intern;
//! let x = Intern::new("hello");
//! let y = Intern::new("world");
//! assert_ne!(x, y);
//! ```

// Enable the `doc_cfg` feature when the `docsrs` configuration attribute is
// defined
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg(test)]
#[cfg(feature = "tinyset")]
use quickcheck::quickcheck;

mod boxedset;
use boxedset::HashSet;
use std::borrow::Borrow;
use std::convert::AsRef;
use std::fmt::{Debug, Display, Pointer};
use std::hash::{Hash, Hasher};
use std::ops::Deref;

mod container;

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

/// A pointer to an interned object that has been leaked and may be used in any
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

impl<T> Clone for Intern<T> {
    fn clone(&self) -> Self {
        Intern {
            pointer: self.pointer,
        }
    }
}

/// An `Intern` is `Copy`, which is unusal for a pointer.  This is safe
/// because we never free the data pointed to by an `Intern`.
impl<T> Copy for Intern<T> {}

impl<T: ?Sized> Intern<T> {
    fn get_pointer(&self) -> *const T {
        self.pointer as *const T
    }
}

static INTERN_CONTAINERS: container::Arena = container::Arena::new();

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
    /// Intern a value.  If this value has not previously been
    /// interned, then `new` will allocate a spot for the value on the
    /// heap.  Otherwise, it will return a pointer to the object
    /// previously allocated.
    ///
    /// Note that `Intern::new` is a bit slow, since it needs to check
    /// a `HashSet` protected by a `Mutex`.
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
    /// If this value has not previously been
    /// interned, then `new` will allocate a spot for the value on the
    /// heap and generate that value using `T::from(val)`.
    pub fn from<'a, Q: ?Sized + Eq + Hash + 'a>(val: &'a Q) -> Intern<T>
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
    /// Get a long-lived reference to the data pointed to by an `Intern`, which
    /// is never freed from the intern pool.
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
        INTERN_CONTAINERS.with(|m: &mut HashSet<&'static T>| -> () { m.clear() })
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


#[cfg(feature = "arena")]
pub mod arena;

#[cfg(feature = "arena")]
pub type Arena<T> = arena::Arena<T>;

#[cfg(feature = "arena")]
pub type ArenaIntern<'a, T> = arena::ArenaIntern<'a, T>;


#[cfg(feature = "arc")]
pub mod arc;

#[cfg(feature = "arc")]
pub type ArcIntern<T> = arc::ArcIntern<T>;

impl<T: ?Sized> AsRef<T> for Intern<T> {
    fn as_ref(&self) -> &T {
        self.pointer
    }
}

macro_rules! create_impls_no_new {
    ( $Intern:ident, $testname:ident,
      [$( $lifetimes:lifetime ),*],
      [$( $traits:ident ),*], [$( $newtraits:ident ),*] ) => {

        impl<$( $lifetimes,)* T: $( $traits +)* ?Sized> Deref for $Intern<$( $lifetimes,)* T> {
            type Target = T;
            fn deref(&self) -> &T {
                self.as_ref()
            }
        }

        impl<$( $lifetimes,)* T: $( $traits +)* Display + ?Sized> Display for $Intern<$( $lifetimes,)* T> {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
                self.deref().fmt(f)
            }
        }

        impl<$( $lifetimes,)* T: $( $traits +)* ?Sized> Pointer for $Intern<$( $lifetimes,)* T> {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
                Pointer::fmt(&self.get_pointer(), f)
            }
        }

        /// The hash implementation returns the hash of the pointer
        /// value, not the hash of the value pointed to.  This should
        /// be irrelevant, since there is a unique pointer for every
        /// value, but it *is* observable, since you could compare the
        /// hash of the pointer with hash of the data itself.
        impl<$( $lifetimes,)* T: $( $traits +)* ?Sized> Hash for $Intern<$( $lifetimes,)* T> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.get_pointer().hash(state);
            }
        }

        impl<$( $lifetimes,)* T: $( $traits +)* ?Sized> PartialEq for $Intern<$( $lifetimes,)* T> {
            fn eq(&self, other: &Self) -> bool {
                self.get_pointer() == other.get_pointer()
            }
        }
        impl<$( $lifetimes,)* T: $( $traits +)* ?Sized> Eq for $Intern<$( $lifetimes,)* T> {}

        impl<$( $lifetimes,)* T: $( $traits +)* PartialOrd + ?Sized> PartialOrd for $Intern<$( $lifetimes,)* T> {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                self.as_ref().partial_cmp(other)
            }
            fn lt(&self, other: &Self) -> bool { self.as_ref().lt(other) }
            fn le(&self, other: &Self) -> bool { self.as_ref().le(other) }
            fn gt(&self, other: &Self) -> bool { self.as_ref().gt(other) }
            fn ge(&self, other: &Self) -> bool { self.as_ref().ge(other) }
        }
        impl<$( $lifetimes,)* T: $( $traits +)* Ord + ?Sized> Ord for $Intern<$( $lifetimes,)* T> {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.as_ref().cmp(other)
            }
        }

        #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
		#[cfg(feature = "serde")]
		impl<$( $lifetimes,)* T: $( $traits +)* Serialize> Serialize for $Intern<$( $lifetimes,)* T> {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                self.as_ref().serialize(serializer)
            }
        }
    }
}
macro_rules! create_impls_new {
    ( $Intern:ident, $testname:ident,
      [$( $lifetimes:lifetime ),*],
      [$( $traits:ident ),*], [$( $newtraits:ident ),*] ) => {

        impl<$( $lifetimes,)* T: $( $newtraits +)* 'static> From<T> for $Intern<$( $lifetimes,)* T> {
            fn from(t: T) -> Self {
                $Intern::new(t)
            }
        }
        impl<$( $lifetimes,)* T: $( $newtraits +)* Default + 'static> Default for $Intern<$( $lifetimes,)* T> {
            fn default() -> Self {
                $Intern::new(Default::default())
            }
        }

        #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
		#[cfg(feature = "serde")]
		impl<'de, $( $lifetimes,)* T: $( $newtraits +)* 'static + Deserialize<'de>> Deserialize<'de> for $Intern<$( $lifetimes,)* T> {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                T::deserialize(deserializer).map(|x: T| Self::new(x))
            }
        }

        #[cfg(test)]
        mod $testname {
            use super::$Intern;
            use super::{Borrow,Deref};
            #[test]
            fn eq_string() {
                assert_eq!($Intern::new("hello"), $Intern::new("hello"));
                assert_ne!($Intern::new("goodbye"), $Intern::new("farewell"));
            }
            #[test]
            fn display() {
                let world = $Intern::new("world");
                println!("Hello {}", world);
            }
            #[test]
            fn debug() {
                let world = $Intern::new("world");
                println!("Hello {:?}", world);
            }
            #[test]
            fn has_default() {
                assert_eq!( $Intern::<Option<String>>::default(),
                            $Intern::<Option<String>>::new(None));
            }
            #[test]
            fn can_clone() {
                assert_eq!( $Intern::<Option<String>>::default().clone(),
                            $Intern::<Option<String>>::new(None));
            }
            #[test]
            fn has_borrow() {
                let x = $Intern::<Option<String>>::default();
                let b: &Option<String> = x.borrow();
                assert_eq!( b, $Intern::<Option<String>>::new(None).as_ref());
            }
            #[test]
            fn has_deref() {
                let x = $Intern::<Option<String>>::default();
                let b: &Option<String> = x.as_ref();
                assert_eq!( b, $Intern::<Option<String>>::new(None).deref());
            }
        }
    }
}

create_impls_new!(
    Intern,
    normal_intern_impl_tests,
    [],
    [],
    [Eq, Hash, Send, Sync]
);
create_impls_no_new!(
    Intern,
    normal_intern_impl_tests,
    [],
    [],
    [Eq, Hash, Send, Sync]
);

impl<T: Debug + ?Sized> Debug for Intern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        std::fmt::Debug::fmt(&self.get_pointer(), f)?;
        f.write_str(" : ")?;
        self.deref().fmt(f)
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
