use crate::boxedset::HashSet;
use parking_lot::Mutex;
use std::borrow::Borrow;

pub struct Arena<T> {
    data: Mutex<HashSet<Box<T>>>,
}
pub struct ArenaIntern<'a, T> {
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
impl<T: Eq + std::hash::Hash> Arena<T> {
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