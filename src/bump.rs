use core::{
    borrow::Borrow,
    cell::Cell,
    hash::{BuildHasher, Hash, Hasher},
    ptr::NonNull,
};
use hashbrown::{hash_map::RawEntryMut, HashMap};

#[cfg(test)]
use std::println;

/// A bump-arena for storing interned data
///
/// You can use an `Bump<T>` to intern data of type `T`. This data is then
/// freed when the `Bump` is dropped.
///
/// # Example
/// ```rust
/// use internment::Bump;
/// let arena: Bump<&'static str> = Bump::new();
/// let x = arena.intern("hello");
/// let y = arena.intern("world");
/// assert_ne!(x, y);
/// println!("The conventional greeting is '{} {}'", x, y);
/// ```

#[cfg_attr(docsrs, doc(cfg(feature = "bump")))]
pub struct Bump<T, S = hashbrown::DefaultHashBuilder> {
    arena: bumpalo::Bump,
    interner: Cell<HashMap<Interned<T>, (), S>>,
}

impl<T, S: Default> Bump<T, S> {
    /// Allocate a new `Bump`
    #[inline]
    pub fn new() -> Self {
        Bump {
            arena: bumpalo::Bump::new(),
            interner: Default::default(),
        }
    }
}
impl<T: Eq + Hash, S: Default + BuildHasher> Bump<T, S> {
    /// Intern a value.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the object previously allocated.
    pub fn intern(&self, val: T) -> &T {
        let mut interner = self.interner.take();
        let entry = interner.raw_entry_mut().from_key(&val);
        let r = match entry {
            RawEntryMut::Vacant(v) => {
                let r = &*self.arena.alloc(val);
                v.insert(Interned(NonNull::from(r)), ());
                r
            }
            RawEntryMut::Occupied(o) => {
                let key = o.key();
                // SAFETY: We are creating a ref with the same lifetime as
                // `&self` (the enclosing `Bump`).
                unsafe { key.deref() }
            }
        };
        self.interner.set(interner);
        r
    }
}

impl<T, S: Default> Default for Bump<T, S> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

// Essentially a `&'static T` reference to a value allocated in the `Bump`
// arena. Always safe to deref, but any `&'a T` reference lifetime must be
// linked to the lifetime of the `Bump` arena (i.e. the lifetime of this
// `Interned<T>`).
struct Interned<T>(NonNull<T>);

impl<T> Interned<T> {
    /// SAFETY: always safe to call, however if the lifetime of the resulting
    /// reference must be shorter than the lifetime of the enclosing `Bump`.
    unsafe fn deref<'a>(&self) -> &'a T {
        unsafe { self.0.as_ref() }
    }

    fn borrow(&self) -> &T {
        // SAFETY: The `self: Interned` only exists in the `interner` field. Any
        // (lifetime) reference to it must live as long as the containing
        // `Bump`. This means that the `arena` field must also be live for this
        // duration. Therefore it is safe to hand out a ref to a `T` in that
        // arena.
        unsafe { self.deref() }
    }
}

impl<T> Borrow<T> for Interned<T> {
    fn borrow(&self) -> &T {
        self.borrow()
    }
}

impl<T: PartialEq> PartialEq for Interned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.borrow() == other.borrow()
    }
}
impl<T: Eq> Eq for Interned<T> {}

impl<T: Hash> Hash for Interned<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.borrow().hash(state);
    }
}

#[test]
fn eq_string() {
    let arena = Bump::<&'static str>::new();
    assert_eq!(
        arena.intern("hello") as *const _,
        arena.intern("hello") as *const _
    );
    assert_ne!(
        arena.intern("goodbye") as *const _,
        arena.intern("farewell") as *const _
    );
}
#[test]
fn display() {
    let arena = Bump::<&'static str>::new();
    let world = arena.intern("world");
    println!("Hello {}", world);
}
#[test]
fn debug() {
    let arena = Bump::<&'static str>::new();
    let world = arena.intern("world");
    println!("Hello {:?}", world);
}
