use crate::boxedset::HashSet;
use parking_lot::Mutex;
use std::borrow::Borrow;
use std::hash::{Hash, Hasher};

pub struct Arena<T: ?Sized> {
    data: Mutex<HashSet<Box<T>>>,
}
pub struct ArenaIntern<'a, T: ?Sized> {
    pub pointer: &'a T,
}

impl<'a, T> Clone for ArenaIntern<'a, T> {
    fn clone(&self) -> Self {
        ArenaIntern {
            pointer: self.pointer,
        }
    }
}
impl<'a, T> Copy for ArenaIntern<'a, T> {}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Arena {
            data: Mutex::new(HashSet::new()),
        }
    }
}
impl<T: Eq + Hash> Arena<T> {
    pub fn intern(&self, val: T) -> ArenaIntern<T> {
        let mut m = self.data.lock();
        if let Some(b) = m.get(&val) {
            let p = b.as_ref() as *const T;
            return ArenaIntern {
                pointer: unsafe { &*p },
            };
        }
        let b = Box::new(val);
        let p = b.as_ref() as *const T;
        m.insert(b);
        ArenaIntern {
            pointer: unsafe { &*p },
        }
    }
}
impl<T: Eq + Hash + ?Sized> Arena<T> {
        pub fn intern_ref<'a, 'b, I>(&'a self, val: &'b I) -> ArenaIntern<'a, T>
    where
        T: 'a + Borrow<I> + From<&'b I>,
        I: Eq + std::hash::Hash + ?Sized,
    {
        let mut m = self.data.lock();
        if let Some(b) = m.get(val) {
            let p = b.as_ref() as *const T;
            return ArenaIntern {
                pointer: unsafe { &*p },
            };
        }
        let b: Box<T> = Box::new(val.into());
        let p = b.as_ref() as *const T;
        m.insert(b);
        ArenaIntern {
            pointer: unsafe { &*p },
        }
    }
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T: ?Sized> AsRef<T> for ArenaIntern<'a, T> {
    fn as_ref(&self) -> &T {
        self.pointer
    }
}

impl<'a, T: ?Sized> std::ops::Deref for ArenaIntern<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'a, T: ?Sized> ArenaIntern<'a, T> {
    fn get_pointer(&self) -> *const T {
        self.pointer as *const T
    }
}


/// The hash implementation returns the hash of the pointer
/// value, not the hash of the value pointed to.  This should
/// be irrelevant, since there is a unique pointer for every
/// value, but it *is* observable, since you could compare the
/// hash of the pointer with hash of the data itself.
impl<'a, T: ?Sized> Hash for ArenaIntern<'a, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_pointer().hash(state);
    }
}

impl<'a, T: ?Sized> PartialEq for ArenaIntern<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self.get_pointer() == other.get_pointer()
    }
}
impl<'a, T: ?Sized> Eq for ArenaIntern<'a, T> {}

// #[cfg(feature = "arena")]
// create_impls_no_new!(ArenaIntern, arenaintern_impl_tests, ['a], [Eq, Hash], [Eq, Hash]);

impl<'a, T: std::fmt::Debug + ?Sized> std::fmt::Debug for ArenaIntern<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        std::fmt::Debug::fmt(&self.get_pointer(), f)?;
        f.write_str(" : ")?;
        self.as_ref().fmt(f)
    }
}

impl<'a, T: std::fmt::Display + ?Sized> std::fmt::Display for ArenaIntern<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.as_ref().fmt(f)
    }
}

#[test]
fn eq_string() {
    let arena = Arena::<&'static str>::new();
    assert_eq!(arena.intern("hello"), arena.intern("hello"));
    assert_ne!(arena.intern("goodbye"), arena.intern("farewell"));
}
#[test]
fn display() {
    let arena = Arena::<&'static str>::new();
    let world = arena.intern("world");
    println!("Hello {}", world);
}
#[test]
fn debug() {
    let arena = Arena::<&'static str>::new();
    let world = arena.intern("world");
    println!("Hello {:?}", world);
}
#[test]
fn can_clone() {
    let arena = Arena::<&'static str>::new();
    assert_eq!(arena.intern("hello").clone(), arena.intern("hello"));
}
#[test]
fn has_deref() {
    let arena = Arena::<Option<String>>::new();
    let x = arena.intern(None);
    let b: &Option<String> = x.as_ref();
    use std::ops::Deref;
    assert_eq!(b, arena.intern(None).deref());
}
