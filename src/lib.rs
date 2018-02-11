extern crate state;
extern crate tinyset;

#[macro_use]
extern crate lazy_static;

use std::collections::HashMap;
use std::sync::Mutex;

use std::hash::Hash;
use std::borrow::Borrow;
use std::ops::Deref;
use std::fmt::Debug;

use tinyset::u64set::Fits64;

lazy_static! {
    static ref CONTAINER: state::Container = state::Container::new();
}

#[derive(Eq, PartialEq)]
pub struct Intern<T> {
    pointer: *const T,
}

impl<T> Clone for Intern<T> {
    fn clone(&self) -> Self {
        Intern { pointer: self.pointer }
    }
}
impl<T> Copy for Intern<T> {}

unsafe impl<T> Send for Intern<T> {}
unsafe impl<T> Sync for Intern<T> {}

impl<T: Clone + Eq + Hash + Send + 'static> Intern<T> {
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
