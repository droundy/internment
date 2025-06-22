use core::{
    borrow::Borrow,
    hash::{BuildHasher, Hash, Hasher},
    ops::Deref,
};

#[cfg(all(feature = "deepsize", feature = "alloc"))]
use alloc::boxed::Box;

pub struct HashMap<P, V>(hashbrown::HashMap<P, V>);

impl<P: Deref + Eq + Hash, V> Default for HashMap<P, V> {
    #[inline]
    fn default() -> Self {
        HashMap::new()
    }
}
impl<P, V> HashMap<P, V> {
    #[inline]
    pub fn new() -> Self {
        HashMap(hashbrown::HashMap::new())
    }
}

#[cfg(feature = "deepsize")]
impl<P: deepsize::DeepSizeOf, V: deepsize::DeepSizeOf> deepsize::DeepSizeOf
    for HashMap<&'static P, V>
{
    fn deep_size_of_children(&self, context: &mut deepsize::Context) -> usize {
        let pointers = self.0.capacity() * core::mem::size_of::<&'static P>();
        let heap_memory = self
            .0
            .iter()
            .map(|(_, v)| {
                core::mem::size_of::<P>()
                    + v.deep_size_of_children(context)
                    + core::mem::size_of_val(v)
            })
            .sum::<usize>();
        pointers + heap_memory
    }
}

#[cfg(all(feature = "deepsize", feature = "alloc"))]
impl<P: deepsize::DeepSizeOf + ?Sized, V: deepsize::DeepSizeOf> deepsize::DeepSizeOf
    for HashMap<Box<P>, V>
{
    fn deep_size_of_children(&self, context: &mut deepsize::Context) -> usize {
        let cap = self.0.capacity();
        let pointers = cap * core::mem::size_of::<Box<P>>();
        let heap_memory = self
            .0
            .iter()
            .map(|(n, v)| {
                (**n).deep_size_of_children(context)
                    + core::mem::size_of_val(&**n)
                    + v.deep_size_of_children(context)
                    + core::mem::size_of_val(v)
            })
            .sum::<usize>();
        pointers + heap_memory
    }
}

impl<P: Deref + Eq + Hash, V> HashMap<P, V> {
    pub fn get<Q: ?Sized + Eq + Hash>(&self, key: &Q) -> Option<&V>
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
            .map(|(_, v)| *v)
    }
    #[inline]
    pub fn insert(&mut self, x: P, v: V) {
        self.0.insert(x, v);
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
