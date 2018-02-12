//! The internment crate provides an `Intern<T>` type, which
//! [interns](https://en.wikipedia.org/wiki/String_interning) an
//! object of type `T`.  The `Intern<T>` stores a pointer to the
//! object `T`, with the guarantee that a single data value (as
//! defined by `Eq` and `Hash`) will correspond to a single pointer
//! value.  This means that we can use pointer comparison (and a
//! pointer hash) in place of value comparisons, which is faster.
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
use std::ops::Deref;
use std::fmt::Debug;

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

#[derive(Eq, PartialEq)]
pub struct Intern<T> {
    pointer: *const T,
}

impl<T> Clone for Intern<T> {
    fn clone(&self) -> Self {
        Intern { pointer: self.pointer }
    }
}

/// An `Intern` is copy, which is unusal for a pointer.  This is safe
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
}

impl<T> Borrow<T> for Intern<T> {
    fn borrow(&self) -> &T {
        unsafe { &*self.pointer }
    }
}

impl<T> Deref for Intern<T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.borrow()
    }
}

impl<T: Debug> Debug for Intern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.deref().fmt(f)
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

#[cfg(test)]
mod tests {
    use super::Intern;
    #[test]
    fn eq_numbers() {
        assert_eq!(Intern::new(5), Intern::new(5));
    }
    #[test]
    fn eq_strings() {
        assert_eq!(Intern::new("hello"), Intern::new("hello"));
    }
    #[test]
    fn different_strings() {
        assert_ne!(Intern::new("hello"), Intern::new("world"));
    }
}
