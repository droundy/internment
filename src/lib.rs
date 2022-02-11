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
#[cfg(feature = "arc")]
use dashmap::{mapref::entry::Entry, DashMap};
use parking_lot::Mutex;
#[cfg(feature = "arc")]
use std::sync::atomic::AtomicUsize;
#[cfg(feature = "arc")]
use std::sync::atomic::Ordering;

mod container;
use container::{TypeHolderSend};

use std::any::Any;
use std::any::TypeId;
use std::borrow::Borrow;
use std::convert::AsRef;
use std::fmt::{Debug, Display, Pointer};
use std::hash::{Hash, Hasher};
use std::ops::Deref;

#[cfg(feature = "rkyv")]
use rkyv::{Archive as RkyvArchive, Deserialize as RkyvDeserialize, Serialize as RkyvSerialize};
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
#[test]
#[cfg(feature = "arc")]
fn like_doctest_arcintern() {
    let x = ArcIntern::new("hello".to_string());
    let y = ArcIntern::<String>::from("world");
    assert_ne!(x, y);
    assert_eq!(x, ArcIntern::from("hello"));
    assert_eq!(y, ArcIntern::from("world"));
    assert_eq!(&*x, "hello"); // dereference a Intern like a pointer\
}

/// A pointer to an interned object that has been leaked and may be used in any
/// thread without locking.
pub struct Intern<T: 'static> {
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

#[cfg(feature = "arc")]
#[test]
fn arc_has_niche() {
    assert_eq!(
        std::mem::size_of::<ArcIntern<String>>(),
        std::mem::size_of::<usize>(),
    );
    assert_eq!(
        std::mem::size_of::<Option<ArcIntern<String>>>(),
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

impl<T> Intern<T> {
    fn get_pointer(&self) -> *const T {
        self.pointer as *const T
    }
}

fn with_global<F, T, R>(f: F) -> R
where
    F: FnOnce(&mut T) -> R,
    T: Any + Send + Default,
{
    // Compute the hash of the type.
    fn hash_of_type<T: 'static>() -> u64 {
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
        TypeId::of::<T>().hash(&mut hasher);
        hasher.hash
    }

    const INTERN_CONTAINER_COUNT: usize = 32;
    static INTERN_CONTAINERS: [Mutex<TypeHolderSend>; INTERN_CONTAINER_COUNT] = [
        // There's no way to create a static array without copy-paste.
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
        parking_lot::const_mutex(TypeHolderSend::new()),
    ];
    f(
        INTERN_CONTAINERS[hash_of_type::<T>() as usize % INTERN_CONTAINER_COUNT]
            .lock()
            .get_type_mut(),
    )
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
        with_global(|m: &mut HashSet<&'static T>| -> Intern<T> {
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
        with_global(|m: &mut HashSet<&'static T>| -> Intern<T> {
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
        with_global(|m: &mut HashSet<&'static T>| -> usize { m.len() })
    }

    /// Only for benchmarking, this will cause problems
    #[cfg(feature = "bench")]
    pub fn benchmarking_only_clear_interns() {
        with_global(|m: &mut HashSet<&'static T>| -> () { m.clear() })
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

/// A pointer to a reference-counted interned object.
///
/// This type requires feature "arc".  The interned object will be held in memory only until its
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
///
/// # Example with owned `String` data
///
/// ```rust
/// use internment::ArcIntern;
///
/// let x = ArcIntern::new("hello".to_string());
/// let y = ArcIntern::<String>::from("world");
/// assert_eq!(x, ArcIntern::from("hello"));
/// assert_eq!(&*x, "hello"); // dereference an ArcIntern like a pointer
/// ```
#[cfg_attr(docsrs, doc(cfg(feature = "arc")))]
#[cfg(feature = "arc")]
pub struct ArcIntern<T: Eq + Hash + Send + Sync + 'static> {
    pointer: std::ptr::NonNull<RefCount<T>>,
}

#[cfg(feature = "arc")]
unsafe impl<T: Eq + Hash + Send + Sync> Send for ArcIntern<T> {}
#[cfg(feature = "arc")]
unsafe impl<T: Eq + Hash + Send + Sync> Sync for ArcIntern<T> {}

#[cfg(feature = "arc")]
#[derive(Debug)]
struct RefCount<T> {
    count: AtomicUsize,
    data: T,
}
#[cfg(feature = "arc")]
impl<T: Eq> Eq for RefCount<T> {}
#[cfg(feature = "arc")]
impl<T: PartialEq> PartialEq for RefCount<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}
#[cfg(feature = "arc")]
impl<T: Hash> Hash for RefCount<T> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.data.hash(hasher)
    }
}

#[cfg(feature = "arc")]
#[derive(Eq, PartialEq, Hash)]
struct BoxRefCount<T>(Box<RefCount<T>>);
#[cfg(feature = "arc")]
impl<T> BoxRefCount<T> {
    fn into_inner(self) -> T {
        self.0.data
    }
}
#[cfg(feature = "arc")]
impl<T> Borrow<T> for BoxRefCount<T> {
    fn borrow(&self) -> &T {
        &self.0.data
    }
}
#[cfg(feature = "arc")]
impl<T> Borrow<RefCount<T>> for BoxRefCount<T> {
    fn borrow(&self) -> &RefCount<T> {
        &self.0
    }
}
#[cfg(feature = "arc")]
impl<T> Deref for BoxRefCount<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.0.data
    }
}

#[cfg(feature = "arc")]
use ahash::RandomState;
#[cfg(feature = "arc")]
type Container<T> = DashMap<BoxRefCount<T>, (), RandomState>;
#[cfg(feature = "arc")]
type Untyped = Box<(dyn Any + Send + Sync + 'static)>;

#[cfg(feature = "arc")]
impl<T: Eq + Hash + Send + Sync + 'static> ArcIntern<T> {
    fn get_pointer(&self) -> *const RefCount<T> {
        self.pointer.as_ptr()
    }
    fn get_container() -> dashmap::mapref::one::Ref<'static, TypeId, Untyped, RandomState> {
        use once_cell::sync::OnceCell;
        static ARC_CONTAINERS: OnceCell<DashMap<TypeId, Untyped, RandomState>> = OnceCell::new();
        let type_map = ARC_CONTAINERS.get_or_init(|| DashMap::with_hasher(RandomState::new()));
        // Prefer taking the read lock to reduce contention, only use entry api if necessary.
        let boxed = if let Some(boxed) = type_map.get(&TypeId::of::<T>()) {
            boxed
        } else {
            type_map
                .entry(TypeId::of::<T>())
                .or_insert_with(|| Box::new(Container::<T>::with_hasher(RandomState::new())))
                .downgrade()
        };
        boxed
    }
    /// Intern a value.  If this value has not previously been
    /// interned, then `new` will allocate a spot for the value on the
    /// heap.  Otherwise, it will return a pointer to the object
    /// previously allocated.
    ///
    /// Note that `ArcIntern::new` is a bit slow, since it needs to check
    /// a `DashMap` which is protected by internal sharded locks.
    pub fn new(mut val: T) -> ArcIntern<T> {
        loop {
            let c = Self::get_container();
            let m = c.downcast_ref::<Container<T>>().unwrap();
            if let Some(b) = m.get_mut(&val) {
                let b = b.key();
                // First increment the count.  We are holding the write mutex here.
                // Has to be the write mutex to avoid a race
                let oldval = b.0.count.fetch_add(1, Ordering::SeqCst);
                if oldval != 0 {
                    // we can only use this value if the value is not about to be freed
                    return ArcIntern {
                        pointer: std::ptr::NonNull::from(b.0.borrow()),
                    };
                } else {
                    // we have encountered a race condition here.
                    // we will just wait for the object to finish
                    // being freed.
                    b.0.count.fetch_sub(1, Ordering::SeqCst);
                }
            } else {
                let b = Box::new(RefCount {
                    count: AtomicUsize::new(1),
                    data: val,
                });
                match m.entry(BoxRefCount(b)) {
                    Entry::Vacant(e) => {
                        // We can insert, all is good
                        let p = ArcIntern {
                            pointer: std::ptr::NonNull::from(e.key().0.borrow()),
                        };
                        e.insert(());
                        return p;
                    }
                    Entry::Occupied(e) => {
                        // Race, map already has data, go round again
                        let box_ref_count = e.into_key();
                        val = box_ref_count.into_inner();
                    }
                }
            }
            // yield so that the object can finish being freed,
            // and then we will be able to intern a new copy.
            std::thread::yield_now();
        }
    }
    /// Intern a value from a reference with atomic reference counting.
    ///
    /// If this value has not previously been
    /// interned, then `new` will allocate a spot for the value on the
    /// heap and generate that value using `T::from(val)`.
    pub fn from<'a, Q: ?Sized + Eq + Hash + 'a>(val: &'a Q) -> ArcIntern<T>
    where
        T: Borrow<Q> + From<&'a Q>,
    {
        // No reference only fast-path as
        // the trait `std::borrow::Borrow<Q>` is not implemented for `Arc<T>`
        Self::new(val.into())
    }
    /// See how many objects have been interned.  This may be helpful
    /// in analyzing memory use.
    pub fn num_objects_interned() -> usize {
        let c = Self::get_container();
        c.downcast_ref::<Container<T>>()
            .map(|m| m.len())
            .unwrap_or(0)
    }
    /// Return the number of counts for this pointer.
    pub fn refcount(&self) -> usize {
        unsafe { self.pointer.as_ref().count.load(Ordering::Acquire) }
    }

    /// Only for benchmarking, this will cause problems
    #[cfg(feature = "bench")]
    pub fn benchmarking_only_clear_interns() {}
}

#[cfg(feature = "arc")]
impl<T: Eq + Hash + Send + Sync + 'static> Clone for ArcIntern<T> {
    fn clone(&self) -> Self {
        // First increment the count.  Using a relaxed ordering is
        // alright here, as knowledge of the original reference
        // prevents other threads from erroneously deleting the
        // object.  (See `std::sync::Arc` documentation for more
        // explanation.)
        unsafe { self.pointer.as_ref().count.fetch_add(1, Ordering::Relaxed) };
        ArcIntern {
            pointer: self.pointer,
        }
    }
}

#[cfg(not(test))]
#[cfg(feature = "arc")]
fn yield_on_tests() {}
#[cfg(test)]
#[cfg(feature = "arc")]
fn yield_on_tests() {
    std::thread::yield_now();
}

#[cfg(feature = "arc")]
impl<T: Eq + Hash + Send + Sync> Drop for ArcIntern<T> {
    fn drop(&mut self) {
        // (Quoting from std::sync::Arc again): Because `fetch_sub` is
        // already atomic, we do not need to synchronize with other
        // threads unless we are going to delete the object. This same
        // logic applies to the below `fetch_sub` to the `weak` count.
        let count_was = unsafe { self.pointer.as_ref().count.fetch_sub(1, Ordering::SeqCst) };
        if count_was == 1 {
            // The following causes the code only when testing, to yield
            // control before taking the mutex, which should make it
            // easier to trigger any race condition (and hopefully won't
            // mask any other race conditions).
            yield_on_tests();
            // (Quoting from std::sync::Arc again): This fence is
            // needed to prevent reordering of use of the data and
            // deletion of the data.  Because it is marked `Release`,
            // the decreasing of the reference count synchronizes with
            // this `Acquire` fence. This means that use of the data
            // happens before decreasing the reference count, which
            // happens before this fence, which happens before the
            // deletion of the data.
            std::sync::atomic::fence(Ordering::SeqCst);

            // removed is declared before m, so the mutex guard will be
            // dropped *before* the removed content is dropped, since it
            // might need to lock the mutex.
            let _remove;
            let c = Self::get_container();
            let m = c.downcast_ref::<Container<T>>().unwrap();
            _remove = m.remove(unsafe { self.pointer.as_ref() });
        }
    }
}

#[cfg(feature = "arc")]
impl<T: Send + Sync + Hash + Eq> AsRef<T> for ArcIntern<T> {
    fn as_ref(&self) -> &T {
        unsafe { &self.pointer.as_ref().data }
    }
}
impl<T> AsRef<T> for Intern<T> {
    fn as_ref(&self) -> &T {
        self.pointer
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
                Pointer::fmt(&self.get_pointer(), f)
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
                self.get_pointer().hash(state);
            }
        }

        impl<T: $( $traits +)*> PartialEq for $Intern<T> {
            fn eq(&self, other: &$Intern<T>) -> bool {
                self.get_pointer() == other.get_pointer()
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

        #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
		#[cfg(feature = "serde")]
		impl<T: $( $traits +)* Serialize> Serialize for $Intern<T> {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                self.as_ref().serialize(serializer)
            }
        }

        #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
		#[cfg(feature = "serde")]
		impl<'de, T: $( $newtraits +)* 'static + Deserialize<'de>> Deserialize<'de> for $Intern<T> {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                T::deserialize(deserializer).map(|x: T| Self::new(x))
            }
        }

		#[cfg(feature = "rkyv")]
        impl<T: $( $traits +)* rkyv::Archive> rkyv::Archive for $Intern<T> {
            type Archived = rkyv::Archived<T>;
            type Resolver = rkyv::Resolver<T>;

            #[allow(clippy::unit_arg)]
            #[inline]
            unsafe fn resolve(&self, pos: usize, resolver: Self::Resolver, out: *mut Self::Archived) {
                self.as_ref().resolve(pos, resolver, out)
            }
        }

		#[cfg(feature = "rkyv")]
        impl<T: $( $traits +)* RkyvSerialize<S>, S: rkyv::Fallible + ?Sized> RkyvSerialize<S> for $Intern<T>
        {
            #[inline]
            fn serialize(&self, serializer: &mut S) -> Result<Self::Resolver, S::Error> {
                RkyvSerialize::serialize(self.as_ref(), serializer)
            }
        }

		#[cfg(feature = "rkyv")]
        impl<T: Eq + Hash + Sync + Send + $( $traits +)* rkyv::Archive<Archived = impl RkyvDeserialize<T, D>> + 'static, D: rkyv::Fallible + ?Sized> RkyvDeserialize<$Intern<T>, D> for rkyv::Archived<$Intern<T>>
        {
            #[inline]
            fn deserialize(&self, deserializer: &mut D) -> Result<$Intern<T>, D::Error> {
                RkyvDeserialize::<T, D>::deserialize(self, deserializer).map($Intern::new)
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

#[cfg(feature = "arc")]
create_impls!(
    ArcIntern,
    arcintern_impl_tests,
    [Eq, Hash, Send, Sync],
    [Eq, Hash, Send, Sync]
);
create_impls!(Intern, normal_intern_impl_tests, [], [Eq, Hash, Send, Sync]);

impl<T: Debug> Debug for Intern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        std::fmt::Debug::fmt(&self.get_pointer(), f)?;
        f.write_str(" : ")?;
        self.deref().fmt(f)
    }
}
#[cfg(feature = "arc")]
impl<T: Eq + Hash + Send + Sync + Debug> Debug for ArcIntern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        Pointer::fmt(&self.pointer, f)?;
        f.write_str(" : ")?;
        self.deref().fmt(f)
    }
}

#[test]
#[cfg(feature = "arc")]
fn test_arcintern_freeing() {
    assert_eq!(ArcIntern::<i32>::num_objects_interned(), 0);
    assert_eq!(ArcIntern::new(5), ArcIntern::new(5));
    {
        let _interned = ArcIntern::new(6);
        assert_eq!(ArcIntern::<i32>::num_objects_interned(), 1);
    }
    {
        let _interned = ArcIntern::new(6);
        assert_eq!(ArcIntern::<i32>::num_objects_interned(), 1);
    }
    {
        let _interned = ArcIntern::new(7);
        assert_eq!(ArcIntern::<i32>::num_objects_interned(), 1);
    }

    let six = ArcIntern::new(6);

    {
        let _interned = ArcIntern::new(7);
        assert_eq!(ArcIntern::<i32>::num_objects_interned(), 2);
    }
    assert_eq!(ArcIntern::new(6), six);
}

#[cfg(feature = "arc")]
#[test]
fn test_arcintern_nested_drop() {
    #[derive(PartialEq, Eq, Hash)]
    enum Nat {
        Zero,
        Successor(ArcIntern<Nat>),
    }
    let zero = ArcIntern::new(Nat::Zero);
    let _one = ArcIntern::new(Nat::Successor(zero));
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

// Quickly create and destroy a small number of interned objects from
// multiple threads.
#[cfg(feature = "arc")]
#[test]
fn multithreading1() {
    use std::sync::Arc;
    use std::thread;
    let mut thandles = vec![];
    let drop_check = Arc::new(true);
    for _i in 0..10 {
        thandles.push(thread::spawn({
            let drop_check = drop_check.clone();
            move || {
                for _i in 0..100_000 {
                    let _interned1 =
                        ArcIntern::new(TestStructCount("foo".to_string(), 5, drop_check.clone()));
                    let _interned2 =
                        ArcIntern::new(TestStructCount("bar".to_string(), 10, drop_check.clone()));
                }
            }
        }));
    }
    for h in thandles.into_iter() {
        h.join().unwrap()
    }
    assert_eq!(Arc::strong_count(&drop_check), 1);
    assert_eq!(ArcIntern::<TestStructCount>::num_objects_interned(), 0);
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