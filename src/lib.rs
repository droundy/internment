// Copyright 2018 David Roundy
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
//! You have three options with the internment crate:
//!
//! 1. `Intern`, which will never free your data.  This means that an
//! `Intern` is `Copy`, so you can make as many copies of the pointer
//! as you may care to at no cost.
//!
//! 2. `LocalIntern`, which will only free your data when the calling
//! thread exits.  This means that a `LocalIntern` is `Copy`, so you can
//! make as many copies of the pointer as you may care to at no cost.
//! However, you cannot share a `LocalIntern` with another thread.  On the
//! plus side, it is faster to create a `LocalIntern` than an `Intern`.
//!
//! 3. `ArcIntern`, which reference-counts your data and frees it when
//! there are no more references.  `ArcIntern` will keep memory use
//! down, but uses an atomic increment/decrement whenever a clone of
//! your pointer is made, or a pointer is dropped.
//!
//! In each case, accessing your data is a single pointer dereference, and
//! the size of any internment data structure (`Intern`, `LocalIntern`, or
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

#[cfg(test)]
use quickcheck::quickcheck;

use lazy_static::lazy_static;

use std::collections::{HashSet};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::cell::RefCell;

use std::any::Any;
use std::hash::{Hash, Hasher};
use std::borrow::Borrow;
use std::convert::AsRef;
use std::ops::Deref;
use std::fmt::{Debug, Display, Pointer};
use std::marker::PhantomData;

use tinyset::Fits64;
use serde::{Serialize, Serializer, Deserialize, Deserializer};

lazy_static! {
    static ref CONTAINER: state::Container = state::Container::new();
}

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

pub struct Intern<T> {
    pointer: *const T,
}

impl<T> Clone for Intern<T> {
    fn clone(&self) -> Self {
        Intern { pointer: self.pointer }
    }
}

/// An `Intern` is `Copy`, which is unusal for a pointer.  This is safe
/// because we never free the data pointed to by an `Intern`.
impl<T> Copy for Intern<T> {}

unsafe impl<T> Send for Intern<T> {}
unsafe impl<T> Sync for Intern<T> {}

impl<T: Eq + Hash + Send + 'static> Intern<T> {
    /// Intern a value.  If this value has not previously been
    /// interned, then `new` will allocate a spot for the value on the
    /// heap.  Otherwise, it will return a pointer to the object
    /// previously allocated.
    ///
    /// Note that `Intern::new` is a bit slow, since it needs to check
    /// a `HashSet` protected by a `Mutex`.
    pub fn new(val: T) -> Intern<T> {
        let mut m = match CONTAINER.try_get::<Mutex<HashSet<Box<T>>>>() {
            Some(m) => m,
            None => {
                CONTAINER.set::<Mutex<HashSet<Box<T>>>>(Mutex::new(HashSet::<Box<T>>::new()));
                CONTAINER.get::<Mutex<HashSet<Box<T>>>>()
            },
        }.lock().unwrap();
        if let Some(b) = m.get(&val) {
            return Intern { pointer: b.borrow() };
        }
        let b = Box::new(val);
        let p: *const T = b.borrow();
        m.insert(b);
        return Intern { pointer: p };
    }
    /// See how many objects have been interned.  This may be helpful
    /// in analyzing memory use.
    pub fn num_objects_interned(&self) -> usize {
        if let Some(m) = CONTAINER.try_get::<Mutex<HashSet<Box<T>>>>() {
            return m.lock().unwrap().len();
        }
        0
    }
}

fn heap_location() -> u64 {
    lazy_static! {
        static ref HEAP_LOCATION: Box<usize> = Box::new(0);
    }
    let p: *const usize = (*HEAP_LOCATION).borrow();
    p as u64
}
fn sz<T>() -> u64 {
    std::mem::align_of::<T>() as u64
}
/// The `Fits64` implementation for `Intern<T>` is designed to
/// normally give (relatively) small numbers, by XORing with a fixed
/// pointer that is also on the heap.  This should make the most
/// significant bits of the resulting u64 be zero, which will mean
/// that `Set64` (which is space-efficient in storing small integers)
/// can store this result in fewer than 8 bytes.
impl<T: Debug> Fits64 for Intern<T> {
    unsafe fn from_u64(x: u64) -> Self {
        Intern { pointer: ((x ^ heap_location() / sz::<T>()) * sz::<T>() ) as *const T }
    }
    fn to_u64(self) -> u64 {
        self.pointer as u64 / sz::<T>() ^ heap_location() / sz::<T>()
    }
}
/// The `Fits64` implementation for `LocalIntern<T>` is designed to
/// normally give (relatively) small numbers, by XORing with a fixed
/// pointer that is also on the heap.  This should make the most
/// significant bits of the resulting u64 be zero, which will mean
/// that `Set64` (which is space-efficient in storing small integers)
/// can store this result in fewer than 8 bytes.
impl<T: Debug> Fits64 for LocalIntern<T> {
    unsafe fn from_u64(x: u64) -> Self {
        LocalIntern { pointer: ((x ^ heap_location() / sz::<T>()) * sz::<T>() ) as *const T }
    }
    fn to_u64(self) -> u64 {
        self.pointer as u64 / sz::<T>() ^ heap_location() / sz::<T>()
    }
}
#[test]
fn test_localintern_set64() {
    use tinyset::Set64;
    let mut s = Set64::<LocalIntern<u32>>::new();
    s.insert(LocalIntern::new(5));
    s.insert(LocalIntern::new(6));
    s.insert(LocalIntern::new(6));
    s.insert(LocalIntern::new(7));
    assert!(s.contains(LocalIntern::new(5)));
    assert!(s.contains(LocalIntern::new(6)));
    assert!(s.contains(LocalIntern::new(7)));
    assert!(!s.contains(LocalIntern::new(8)));
    assert_eq!(s.len(), 3);
}
#[test]
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

/// A pointer to a reference-counted interned object.
///
/// The interned object will be held in memory only until its
/// reference count reaches zero.
///
/// # Example
/// ```rust
/// use internment::ArcIntern;
///
/// let x = ArcIntern::new("hello");
/// let y = ArcIntern::new("world");
/// assert_ne!(x, y);
/// assert_eq!(x, ArcIntern::new("hello"));
/// assert_eq!(*x, "hello"); // dereference an ArcIntern like a pointer
/// ```
pub struct ArcIntern<T: Eq + Hash + Send + 'static> {
    pointer: *const RefCount<T>,
}

unsafe impl<T: Eq+Hash+Send> Send for ArcIntern<T> {}
unsafe impl<T: Eq+Hash+Send> Sync for ArcIntern<T> {}

#[derive(Debug)]
struct RefCount<T> {
    count: AtomicUsize,
    data: T,
}
impl<T: Eq> Eq for RefCount<T> {}
impl<T: PartialEq> PartialEq for RefCount<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}
impl<T: Hash> Hash for RefCount<T> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.data.hash(hasher)
    }
}
impl<T> Borrow<T> for Box<RefCount<T>> {
    fn borrow(&self) -> &T {
        &self.data
    }
}

type Container<T> = Mutex<HashSet<Box<RefCount<T>>>>;
impl<T: Eq + Hash + Send + 'static> ArcIntern<T> {
    fn get_mutex() -> &'static Container<T> {
        match CONTAINER.try_get::<Container<T>>() {
            Some(m) => m,
            None => {
                CONTAINER.set::<Container<T>>(Mutex::new(HashSet::new()));
                CONTAINER.get::<Container<T>>()
            },
        }
    }
    /// Intern a value.  If this value has not previously been
    /// interned, then `new` will allocate a spot for the value on the
    /// heap.  Otherwise, it will return a pointer to the object
    /// previously allocated.
    ///
    /// Note that `ArcIntern::new` is a bit slow, since it needs to check
    /// a `HashMap` protected by a `Mutex`.
    pub fn new(val: T) -> ArcIntern<T> {
        let mymutex = Self::get_mutex();
        let mut m = mymutex.lock().unwrap();
        if let Some(b) = m.get(&val) {
            // First increment the count.  We can use relaxed ordering
            // here because we are holding the mutex, which has its
            // own barriers.
            b.count.fetch_add(1, Ordering::Relaxed);
            // then return the value
            return ArcIntern { pointer: b.borrow() };
        }
        let b = Box::new(RefCount { count: AtomicUsize::new(1), data: val });
        let p = ArcIntern { pointer: b.borrow() };
        m.insert(b);
        p
    }
    /// See how many objects have been interned.  This may be helpful
    /// in analyzing memory use.
    pub fn num_objects_interned(&self) -> usize {
        if let Some(m) = CONTAINER.try_get::<Container<T>>() {
            return m.lock().unwrap().len();
        }
        0
    }
    /// Return the number of counts for this pointer.
    pub fn refcount(&self) -> usize {
        unsafe { (*self.pointer).count.load(Ordering::Acquire) }
    }
}

impl<T: Eq + Hash + Send + 'static> Clone for ArcIntern<T> {
    fn clone(&self) -> Self {
        // First increment the count.  Using a relaxed ordering is
        // alright here, as knowledge of the original reference
        // prevents other threads from erroneously deleting the
        // object.  (See `std::sync::Arc` documentation for more
        // explanation.)
        unsafe { (*self.pointer).count.fetch_add(1, Ordering::Relaxed) };
        ArcIntern { pointer: self.pointer }
    }
}

impl<T: Eq + Hash + Send> Drop for ArcIntern<T> {
    fn drop(&mut self) {
        // (Quoting from std::sync::Arc again): Because `fetch_sub` is
        // already atomic, we do not need to synchronize with other
        // threads unless we are going to delete the object. This same
        // logic applies to the below `fetch_sub` to the `weak` count.
        let count_was = unsafe { (*self.pointer).count.fetch_sub(1, Ordering::Release) };
        if count_was == 1 {
            // (Quoting from std::sync::Arc again): This fence is
            // needed to prevent reordering of use of the data and
            // deletion of the data.  Because it is marked `Release`,
            // the decreasing of the reference count synchronizes with
            // this `Acquire` fence. This means that use of the data
            // happens before decreasing the reference count, which
            // happens before this fence, which happens before the
            // deletion of the data.
            std::sync::atomic::fence(Ordering::Acquire);

            // removed is declared before m, so the mutex guard will be
            // dropped *before* the removed content is dropped, since it
            // might need to lock the mutex.
            let mut _removed;
            let mut m = Self::get_mutex().lock().unwrap();
            _removed = m.take(self.as_ref());
        }
    }
}

impl<T: Send + Hash + Eq> AsRef<T> for ArcIntern<T> {
    fn as_ref(&self) -> &T {
        unsafe { &(*self.pointer).data }
    }
}
impl<T> AsRef<T> for Intern<T> {
    fn as_ref(&self) -> &T {
        unsafe { &*self.pointer }
    }
}
impl<T> AsRef<T> for LocalIntern<T> {
    fn as_ref(&self) -> &T {
        unsafe { &*self.pointer }
    }
}
macro_rules! create_impls {
    ( $Intern:ident, $testname:ident,
      [$( $traits:ident ),*], [$( $newtraits:ident ),*] ) => {

        impl<T: $( $traits +)*> Borrow<T> for $Intern<T> {
            fn borrow(&self) -> &T {
                self.as_ref()
            }
        }
        impl<T: $( $traits +)*> Deref for $Intern<T> {
            type Target = T;
            fn deref(&self) -> &T {
                self.as_ref()
            }
        }

        impl<T: $( $traits +)* Display> Display for $Intern<T> {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
                self.deref().fmt(f)
            }
        }

        impl<T: $( $traits +)*> Pointer for $Intern<T> {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
                Pointer::fmt(&self.pointer, f)
            }
        }

        impl<T: $( $newtraits +)* 'static> From<T> for $Intern<T> {
            fn from(t: T) -> Self {
                $Intern::new(t)
            }
        }
        impl<T: $( $newtraits +)* Default + 'static> Default for $Intern<T> {
            fn default() -> $Intern<T> {
                $Intern::new(Default::default())
            }
        }

        /// The hash implementation returns the hash of the pointer
        /// value, not the hash of the value pointed to.  This should
        /// be irrelevant, since there is a unique pointer for every
        /// value, but it *is* observable, since you could compare the
        /// hash of the pointer with hash of the data itself.
        impl<T: $( $traits +)*> Hash for $Intern<T> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.pointer.hash(state);
            }
        }

        impl<T: $( $traits +)*> PartialEq for $Intern<T> {
            fn eq(&self, other: &$Intern<T>) -> bool {
                self.pointer == other.pointer
            }
        }
        impl<T: $( $traits +)*> Eq for $Intern<T> {}

        impl<T: $( $traits +)* PartialOrd> PartialOrd for $Intern<T> {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                self.as_ref().partial_cmp(other)
            }
            fn lt(&self, other: &Self) -> bool { self.as_ref().lt(other) }
            fn le(&self, other: &Self) -> bool { self.as_ref().le(other) }
            fn gt(&self, other: &Self) -> bool { self.as_ref().gt(other) }
            fn ge(&self, other: &Self) -> bool { self.as_ref().ge(other) }
        }
        impl<T: $( $traits +)* Ord> Ord for $Intern<T> {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.as_ref().cmp(other)
            }
        }

        impl<T: $( $traits +)* Serialize> Serialize for $Intern<T> {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                self.as_ref().serialize(serializer)
            }
        }

        impl<'de, T: $( $newtraits +)* 'static + Deserialize<'de>> Deserialize<'de> for $Intern<T> {
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

create_impls!(ArcIntern, arcintern_impl_tests, [Eq,Hash,Send], [Eq,Hash,Send] );
create_impls!(Intern, intern_impl_tests, [], [Eq,Hash,Send]);
create_impls!(LocalIntern, localintern_impl_tests, [], [Eq,Hash]);

impl<T: Debug> Debug for Intern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        std::fmt::Display::fmt(&self.to_u64(), f)?;
        f.write_str(" : ")?;
        self.deref().fmt(f)
    }
}
impl<T: Debug> Debug for LocalIntern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        std::fmt::Display::fmt(&self.to_u64(), f)?;
        f.write_str(" : ")?;
        self.deref().fmt(f)
    }
}
impl<T: Eq+Hash+Send+Debug> Debug for ArcIntern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        Pointer::fmt(&self.pointer, f)?;
        f.write_str(" : ")?;
        self.deref().fmt(f)
    }
}


#[test]
fn test_arcintern_freeing() {
    assert_eq!(ArcIntern::new(5), ArcIntern::new(5));
    assert_eq!(ArcIntern::new(6).num_objects_interned(), 1);
    assert_eq!(ArcIntern::new(6).num_objects_interned(), 1);
    assert_eq!(ArcIntern::new(7).num_objects_interned(), 1);
    let six = ArcIntern::new(6);
    assert_eq!(ArcIntern::new(7).num_objects_interned(), 2);
    assert_eq!(ArcIntern::new(6), six);
}

#[test]
fn test_arcintern_nested_drop() {
    #[derive(PartialEq, Eq, Hash)]
    enum Nat {
        Zero,
        Successor(ArcIntern<Nat>)
    }
    let zero = ArcIntern::new(Nat::Zero);
    let _one = ArcIntern::new(Nat::Successor(zero));
}

#[test]
fn test_intern_num_objects() {
    assert_eq!(Intern::new(5), Intern::new(5));
    assert_eq!(Intern::new(6).num_objects_interned(), 2);
    assert_eq!(Intern::new(6).num_objects_interned(), 2);
    assert_eq!(Intern::new(7).num_objects_interned(), 3);
}


/// A pointer to a thread-local interned object.
///
/// The interned object will be held in memory as long as the thread
/// is still running.  Thus you can arrange a crude sort of arena
/// allocation by running code using `LocalIntern` on a temporary
/// thread.  Lifetime issues are as simple as when using `Intern`.
/// `LocalIntern` differs in that it is neigher `Send` nor `Share`, so
/// it cannot be used in a multithreaded manner.  On the benefit side,
/// it is faster than `Intern`, and the memory can be freed (by
/// running in a temporary thread).
///
/// # Example
/// ```rust
/// use internment::LocalIntern;
///
/// let x = LocalIntern::new("hello");
/// let y = LocalIntern::new("world");
/// assert_ne!(x, y);
/// assert_eq!(x, LocalIntern::new("hello"));
/// assert_eq!(*x, "hello"); // dereference a LocalIntern like a pointer
/// ```
pub struct LocalIntern<T> {
    pointer: *const T,
}

impl<T> Clone for LocalIntern<T> {
    fn clone(&self) -> Self {
        LocalIntern { pointer: self.pointer }
    }
}

thread_local! {
    #[allow(unused)]
    pub static LOCAL_STUFF: RefCell<Vec<Box<dyn Any>>> = RefCell::new(Vec::new());
}
pub fn with_local<F, T, R>(f: F) -> R
    where F: FnOnce(&mut T) -> R,
          T: Any+Default
{
    LOCAL_STUFF.with(|v| -> R {
        for x in v.borrow_mut().iter_mut() {
            if let Some(xx) = x.downcast_mut() {
                return f(xx)
            }
        }
        let mut b = Box::new(T::default());
        let r = f(&mut b);
        v.borrow_mut().push(b);
        r
    })
}

/// An `LocalIntern` is `Copy`, which is unusal for a pointer.  This
/// is safe because we never free the data pointed to by an
/// `LocalIntern` until the thread itself is destroyed.
impl<T> Copy for LocalIntern<T> {}

impl<T: Eq + Hash + 'static> LocalIntern<T> {
    /// Intern a value in a thread-local way.  If this value has not
    /// previously been interned, then `new` will allocate a spot for
    /// the value on the heap.  Otherwise, it will return a pointer to
    /// the object previously allocated.
    ///
    /// Note that `LocalIntern::new` is a bit slow, since it needs to check
    /// a `HashMap` protected by a `Mutex`.
    pub fn new(val: T) -> LocalIntern<T> {
        with_local(|m: &mut HashSet<Box<T>>| -> LocalIntern<T> {
            if let Some(ref b) = m.get(&val) {
                return LocalIntern { pointer: (*b).borrow() };
            }
            let b = Box::new(val);
            let p: *const T = b.borrow();
            m.insert(b);
            LocalIntern { pointer: p }
        })
    }
    /// See how many objects have been interned.  This may be helpful
    /// in analyzing memory use.
    pub fn num_objects_interned(&self) -> usize {
        with_local(|m: &mut HashSet<Box<T>>| -> usize {
            m.len()
        })
    }
}

#[test]
fn test_localintern_num_objects() {
    assert_eq!(LocalIntern::new(5), LocalIntern::new(5));
    assert_eq!(LocalIntern::new(6).num_objects_interned(), 2);
    assert_eq!(LocalIntern::new(6).num_objects_interned(), 2);
    assert_eq!(LocalIntern::new(7).num_objects_interned(), 3);
}

#[cfg(test)]
quickcheck! {
    fn fits64_localintern(s: String) -> bool {
        tinyset::set64::test_fits64(LocalIntern::new(s));
        true
    }
    fn fits64_intern(s: String) -> bool {
        tinyset::set64::test_fits64(Intern::new(s));
        true
    }
}

pub struct InternTable<T> {
    vals: HashSet<Box<T>>,
}

impl<T: Eq + Hash> InternTable<T> {
    pub fn intern<'a>(&'a mut self, val: T) -> EntryIntern<'a, T> {
        EntryIntern {
            pointer: if let Some(ref b) = self.vals.get(&val) {
                (*b).borrow()
            } else {
                let b = Box::new(val);
                let p: *const T = b.borrow();
                self.vals.insert(b);
                p
            },
            _phantom: PhantomData,
        }
    }

    pub fn num_objects_interned(&self) -> usize {
        self.vals.len()
    }
}

pub struct EntryIntern<'a, T> {
    pointer: *const T,
    _phantom: PhantomData<&'a ()>,
}

impl<'a, T> Clone for EntryIntern<'a, T> {
    fn clone(&self) -> Self {
        EntryIntern { pointer: self.pointer, _phantom: PhantomData }
    }
}

impl<'a, T> AsRef<T> for EntryIntern<'a, T> {
    fn as_ref(&self) -> &T {
        unsafe { &*self.pointer }
    }
}

impl<'a, T> Borrow<T> for EntryIntern<'a, T> {
    fn borrow(&self) -> &T {
        self.as_ref()
    }
}

impl<'a, T> Deref for EntryIntern<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<'a, T: Display> Display for EntryIntern<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.deref().fmt(f)
    }
}

impl<'a, T> Pointer for EntryIntern<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        Pointer::fmt(&self.pointer, f)
    }
}

/// The hash implementation returns the hash of the pointer
/// value, not the hash of the value pointed to.  This should
/// be irrelevant, since there is a unique pointer for every
/// value, but it *is* observable, since you could compare the
/// hash of the pointer with hash of the data itself.
impl<'a, T> Hash for EntryIntern<'a, T> {
    /// Note that the same values interned in different tables will not have the same hash.
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.pointer.hash(state);
    }
}

impl<'a, T> PartialEq for EntryIntern<'a, T> {
    /// Note that the same values interned in different tables are not considered equal.
    fn eq(&self, other: &Self) -> bool {
        self.pointer == other.pointer
    }
}

impl<'a, T> Eq for EntryIntern<'a, T> {}

impl<'a, T: PartialOrd> PartialOrd for EntryIntern<'a, T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_ref().partial_cmp(other)
    }
    fn lt(&self, other: &Self) -> bool { self.as_ref().lt(other) }
    fn le(&self, other: &Self) -> bool { self.as_ref().le(other) }
    fn gt(&self, other: &Self) -> bool { self.as_ref().gt(other) }
    fn ge(&self, other: &Self) -> bool { self.as_ref().ge(other) }
}

impl<'a, T: Ord> Ord for EntryIntern<'a, T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_ref().cmp(other)
    }
}

impl<'a, T: Serialize> Serialize for EntryIntern<'a, T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_ref().serialize(serializer)
    }
}
