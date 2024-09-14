use core::ops::Deref;
use hashbrown::HashMap;
use std::{
    borrow::Borrow, hash::{BuildHasher, Hash, Hasher}
};
pub struct HashSet<P>(HashMap<P, ()>);

impl<P: Deref + Eq + Hash> Default for HashSet<P> {
    #[inline]
    fn default() -> Self {
        HashSet::new()
    }
}
impl<P> HashSet<P> {
    #[inline]
    pub fn new() -> Self {
        HashSet(HashMap::new())
    }
}

#[cfg(feature = "deepsize")]
impl<P: deepsize::DeepSizeOf> deepsize::DeepSizeOf for HashSet<&'static P> {
    fn deep_size_of_children(&self, context: &mut deepsize::Context) -> usize {
        let pointers = self.0.capacity() * std::mem::size_of::<&'static P>();
        let heap_memory = self
            .0
            .keys()
            .map(|n| (**n).deep_size_of_children(context) + std::mem::size_of::<P>())
            .sum::<usize>();
        pointers + heap_memory
    }
}

#[cfg(feature = "deepsize")]
impl<P: deepsize::DeepSizeOf + ?Sized> deepsize::DeepSizeOf for HashSet<Box<P>> {
    fn deep_size_of_children(&self, context: &mut deepsize::Context) -> usize {
        let pointers = self.0.capacity() * std::mem::size_of::<Box<P>>();
        let heap_memory = self
            .0
            .keys()
            .map(|n| (**n).deep_size_of_children(context) + std::mem::size_of_val(&**n))
            .sum::<usize>();
        pointers + heap_memory
    }
}

impl<P: Deref + Eq + Hash> HashSet<P> {
    pub fn get<'a, Q: ?Sized + Eq + Hash>(&'a self, key: &Q) -> Option<&'a P>
    where
        P::Target: Borrow<Q>,
    {
        let hash = {
            let mut hasher = self.0.hasher().build_hasher();
            key.hash(&mut hasher);
            hasher.finish()
        };
        self.0
            .raw_entry()
            .from_hash(hash, |k| <P::Target as Borrow<Q>>::borrow(k) == key)
            .as_ref()
            .map(|kv| kv.0)
    }
    pub fn _take<Q: ?Sized + Hash + Eq>(&mut self, k: &Q) -> Option<P>
    where
        P: Borrow<Q>,
    {
        self.0.remove_entry(k).map(|(a, ())| a)
        // let hash = {
        //     let mut hasher = self.0.hasher().build_hasher();
        //     key.hash(&mut hasher);
        //     hasher.finish()
        // };
        // let x = self.0.raw_entry_mut().from_hash(hash, |k| <P::Target as Borrow<Q>>::borrow(k) == key)
    }
    #[inline]
    pub fn insert(&mut self, x: P) {
        self.0.insert(x, ());
    }
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }
    #[allow(dead_code)] // maybe unused without `deepsize` feature
    #[inline]
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }
    #[cfg(feature = "bench")]
    #[inline]
    pub fn clear(&mut self) {
        self.0.clear()
    }
}
