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
//! down, but requires locking whenever a clone of your pointer is
//! made, as well as when dropping the pointer.
//!
//! In both cases, accessing your data is a single pointer
//! dereference, and the size of either `Intern` or `ArcIntern` is a
//! single pointer.  In both cases, you have a guarantee that a single
//! data value (as defined by `Eq` and `Hash`) will correspond to a
//! single pointer value.  This means that we can use pointer
//! comparison (and a pointer hash) in place of value comparisons,
//! which is very fast.
//!
//! # Example
//! ```rust
//! use internment::Intern;
//! let x = Intern::new("hello");
//! let y = Intern::new("world");
//! assert_ne!(x, y);
//! ```

extern crate state;
extern crate tinyset;

#[macro_use]
extern crate lazy_static;

use std::collections::HashMap;
use std::sync::Mutex;

use std::hash::{Hash, Hasher};
use std::borrow::Borrow;
use std::convert::AsRef;
use std::ops::Deref;
use std::fmt::{Debug, Display, Pointer};

use tinyset::u64set::Fits64;

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

impl<T> PartialEq for Intern<T> {
    fn eq(&self, other: &Intern<T>) -> bool {
        self.pointer == other.pointer
    }
}
impl<T> Eq for Intern<T> {}

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

impl<T: Clone + Eq + Hash + Send + 'static> Intern<T> {
    /// Intern a value.  If this value has not previously been
    /// interned, then `new` will allocate a spot for the value on the
    /// heap.  Otherwise, it will return a pointer to the object
    /// previously allocated.
    ///
    /// Note that `Intern::new` is a bit slow, since it needs to check
    /// a `HashMap` protected by a `Mutex`.
    pub fn new(val: T) -> Intern<T> {
        if CONTAINER.try_get::<Mutex<HashMap<T,Box<T>>>>().is_none() {
            CONTAINER.set::<Mutex<HashMap<T,Box<T>>>>(Mutex::new(HashMap::<T,Box<T>>::new()));
        }
        let mut m = CONTAINER.get::<Mutex<HashMap<T,Box<T>>>>().lock().unwrap();
        if m.get(&val).is_none() {
            m.insert(val.clone(), Box::new(val.clone()));
        }
        Intern { pointer: m.get(&val).unwrap().borrow() }
    }
    /// See how many objects have been interned.  This may be helpful
    /// in analyzing memory use.
    pub fn num_objects_interned(&self) -> usize {
        if let Some(m) = CONTAINER.try_get::<Mutex<HashMap<T,Box<T>>>>() {
            return m.lock().unwrap().len();
        }
        0
    }
}

impl<T> Borrow<T> for Intern<T> {
    fn borrow(&self) -> &T {
        self.as_ref()
    }
}
impl<T> AsRef<T> for Intern<T> {
    fn as_ref(&self) -> &T {
        unsafe { &*self.pointer }
    }
}

impl<T> Deref for Intern<T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.borrow()
    }
}

impl<T: Default+Hash+Eq+Clone+Send+'static> Default for Intern<T> {
    fn default() -> Intern<T> {
        Intern::new(Default::default())
    }
}

impl<T: Debug> Debug for Intern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        Pointer::fmt(&self.pointer, f)?;
        f.write_str(" : ")?;
        self.deref().fmt(f)
    }
}

impl<T: Display> Display for Intern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.deref().fmt(f)
    }
}

impl<T> Pointer for Intern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        Pointer::fmt(&self.pointer, f)
    }
}

impl<T: Debug> Fits64 for Intern<T> {
    unsafe fn from_u64(x: u64) -> Self {
        Intern { pointer: x as *const T }
    }
    fn to_u64(self) -> u64 {
        self.pointer as u64
    }
}

/// The hash implementation for `Intern` returns the hash of the
/// pointer value, not the hash of the value pointed to.  This should
/// be irrelevant, since there is a unique pointer for every value,
/// but it *is* observable, since you could compare the pointer of
/// `Intern::new(data)` with `data` itself.
impl<T> Hash for Intern<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.pointer.hash(state);
    }
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

#[derive(Eq, PartialEq)]
pub struct ArcIntern<T: Eq + Hash + Send + 'static> {
    pointer: *const T,
}

unsafe impl<T: Eq+Hash+Send> Send for ArcIntern<T> {}
unsafe impl<T: Eq+Hash+Send> Sync for ArcIntern<T> {}

#[derive(Debug)]
struct RcI<T: Hash+Eq+PartialEq> {
    data: HashMap<T, Box<T>>,
    counts: HashMap<Intern<T>, usize>,
}

impl<T: Clone + Eq + Hash + Send + 'static> ArcIntern<T> {
    /// Intern a value.  If this value has not previously been
    /// interned, then `new` will allocate a spot for the value on the
    /// heap.  Otherwise, it will return a pointer to the object
    /// previously allocated.
    ///
    /// Note that `ArcIntern::new` is a bit slow, since it needs to check
    /// a `HashMap` protected by a `Mutex`.
    pub fn new(val: T) -> ArcIntern<T> {
        let mymutex = match CONTAINER.try_get::<Mutex<RcI<T>>>() {
            Some(m) => m,
            None => {
                CONTAINER.set::<Mutex<RcI<T>>>(Mutex::new(
                    RcI {
                        data: HashMap::<T,Box<T>>::new(),
                        counts: HashMap::<Intern<T>,usize>::new(),
                    }));
                CONTAINER.get::<Mutex<RcI<T>>>()
            },
        };
        let mut m = mymutex.lock().unwrap();
        if m.data.get(&val).is_none() {
            let b = Box::new(val.clone());
            let p: *const T = b.borrow();
            m.counts.insert(Intern { pointer: p }, 1);
            m.data.insert(val.clone(), b);
            return ArcIntern { pointer: p };
        }
        let xx = ArcIntern { pointer: m.data.get(&val).unwrap().borrow() };
        // need to increment the count for this!
        if let Some(mc) = m.counts.get_mut(&Intern{ pointer: xx.pointer }) {
            *mc += 1;
        }
        xx
    }
    /// See how many objects have been interned.  This may be helpful
    /// in analyzing memory use.
    pub fn num_objects_interned(&self) -> usize {
        if let Some(m) = CONTAINER.try_get::<Mutex<RcI<T>>>() {
            return m.lock().unwrap().data.len();
        }
        0
    }
    /// Return the number of counts for this pointer.
    pub fn refcount(&self) -> usize {
        let m = CONTAINER.get::<Mutex<RcI<T>>>().lock().unwrap();
        *m.counts.get(&Intern{ pointer: self.pointer }).unwrap()
    }
}

impl<T: Eq + Hash + Send + 'static> Clone for ArcIntern<T> {
    fn clone(&self) -> Self {
        let mut m = CONTAINER.get::<Mutex<RcI<T>>>().lock().unwrap();
        if let Some(mc) = m.counts.get_mut(&Intern{ pointer: self.pointer }) {
            *mc += 1;
        }
        ArcIntern { pointer: self.pointer }
    }
}

impl<T: Eq + Hash + Send> Drop for ArcIntern<T> {
    fn drop(&mut self) {
        let mut m = CONTAINER.get::<Mutex<RcI<T>>>().lock().unwrap();
        let mut am_finished = false;
        if let Some(mc) = m.counts.get_mut(&Intern{ pointer: self.pointer }) {
            *mc -= 1;
            if *mc == 0 {
                am_finished = true;
            }
        }
        if am_finished {
            m.data.remove(self);
            m.counts.remove(&Intern{ pointer: self.pointer });
        }
    }
}

impl<T: Eq+Hash+Send> Borrow<T> for ArcIntern<T> {
    fn borrow(&self) -> &T {
        self.as_ref()
    }
}
impl<T: Eq+Hash+Send> AsRef<T> for ArcIntern<T> {
    fn as_ref(&self) -> &T {
        unsafe { &*self.pointer }
    }
}

impl<T: Eq+Hash+Send> Deref for ArcIntern<T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.borrow()
    }
}

impl<T: Clone + Eq+Hash+Send+Default> Default for ArcIntern<T> {
    fn default() -> ArcIntern<T> {
        ArcIntern::new(Default::default())
    }
}

impl<T: Clone + Eq+Hash+Send+Debug> Debug for ArcIntern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        Pointer::fmt(&self.pointer, f)?;
        f.write_str(" : ")?;
        // self.refcount().fmt(f)?;
        self.deref().fmt(f)
    }
}

impl<T: Display+Clone+Eq+Hash+Send> Display for ArcIntern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.deref().fmt(f)
    }
}

impl<T: Clone+Eq+Hash+Send> Pointer for ArcIntern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        Pointer::fmt(&self.pointer, f)
    }
}


/// The hash implementation for `ArcIntern` returns the hash of the
/// pointer value, not the hash of the value pointed to.  This should
/// be irrelevant, since there is a unique pointer for every value,
/// but it *is* observable, since you could compare the pointer of
/// `ArcIntern::new(data)` with `data` itself.
impl<T: Eq+Hash+Send> Hash for ArcIntern<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.pointer.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::Intern;
    use super::ArcIntern;
    #[test]
    fn eq_numbers() {
        assert_eq!(Intern::new(5), Intern::new(5));
        assert_eq!(Intern::new(6).num_objects_interned(), 2);
        assert_eq!(Intern::new(6).num_objects_interned(), 2);
        assert_eq!(Intern::new(7).num_objects_interned(), 3);
    }
    #[test]
    fn eq_strings() {
        assert_eq!(Intern::new("hello"), Intern::new("hello"));
        let world = Intern::new("world");
        println!("Hello {}", world);
    }
    #[test]
    fn different_strings() {
        assert_ne!(Intern::new("hello"), Intern::new("world"));
    }

    #[test]
    fn aeq_numbers() {
        assert_eq!(ArcIntern::new(5), ArcIntern::new(5));
        assert_eq!(ArcIntern::new(6).num_objects_interned(), 1);
        assert_eq!(ArcIntern::new(6).num_objects_interned(), 1);
        assert_eq!(ArcIntern::new(7).num_objects_interned(), 1);
        let six = ArcIntern::new(6);
        assert_eq!(ArcIntern::new(7).num_objects_interned(), 2);
        assert_eq!(ArcIntern::new(6), six);
    }
    #[test]
    fn aeq_strings() {
        assert_eq!(ArcIntern::new("hello"), ArcIntern::new("hello"));
        let world = ArcIntern::new("world");
        println!("Hello {}", world);
    }
    #[test]
    fn adifferent_strings() {
        assert_ne!(ArcIntern::new("hello"), ArcIntern::new("world"));
    }
}

pub struct LocalIntern<T> {
    pointer: *const T,
}

impl<T> PartialEq for LocalIntern<T> {
    fn eq(&self, other: &LocalIntern<T>) -> bool {
        self.pointer == other.pointer
    }
}
impl<T> Eq for LocalIntern<T> {}

impl<T> Clone for LocalIntern<T> {
    fn clone(&self) -> Self {
        LocalIntern { pointer: self.pointer }
    }
}

/// An `LocalIntern` is `Copy`, which is unusal for a pointer.  This is safe
/// because we never free the data pointed to by an `LocalIntern`.
impl<T> Copy for LocalIntern<T> {}

impl<T: Clone + Eq + Hash + Send + 'static> LocalIntern<T> {
    /// LocalIntern a value.  If this value has not previously been
    /// interned, then `new` will allocate a spot for the value on the
    /// heap.  Otherwise, it will return a pointer to the object
    /// previously allocated.
    ///
    /// Note that `LocalIntern::new` is a bit slow, since it needs to check
    /// a `HashMap` protected by a `Mutex`.
    pub fn new(val: T) -> LocalIntern<T> {
        if CONTAINER.try_get_local::<Mutex<HashMap<T,Box<T>>>>().is_none() {
            CONTAINER.set_local(|| Mutex::new(HashMap::<T,Box<T>>::new()));
        }
        let mut m = CONTAINER.get_local::<Mutex<HashMap<T,Box<T>>>>().lock().unwrap();
        if m.get(&val).is_none() {
            m.insert(val.clone(), Box::new(val.clone()));
        }
        LocalIntern { pointer: m.get(&val).unwrap().borrow() }
    }
    /// See how many objects have been interned.  This may be helpful
    /// in analyzing memory use.
    pub fn num_objects_interned(&self) -> usize {
        if let Some(m) = CONTAINER.try_get_local::<Mutex<HashMap<T,Box<T>>>>() {
            return m.lock().unwrap().len();
        }
        0
    }
}
