use crate::type_bucket::{type_bucket, TYPE_BUCKETS};
use alloc::{boxed::Box, vec::Vec};
use core::{any::Any, ops::DerefMut};

#[cfg(not(any(feature = "std", feature = "spin")))]
compile_error!(
    "Require either the `std` or spin `features` to be enabled when using the `intern` feature"
);

pub struct TypeHolderSend(Vec<AnySend>);

struct AnySend(Box<dyn Any + Send>);

impl TypeHolderSend {
    pub fn get_type_mut<T: Any + Send + Default>(&mut self) -> &mut T {
        if let Some(i) = self
            .0
            .iter_mut()
            .position(|x| x.0.downcast_mut::<T>().is_some())
        {
            self.0[i].0.downcast_mut().unwrap()
        } else {
            let v: T = Default::default();
            self.0.push(AnySend(Box::new(v)));
            self.0.last_mut().unwrap().0.downcast_mut().unwrap()
        }
    }
    pub const fn new() -> Self {
        TypeHolderSend(Vec::new())
    }
}

struct TypeHolderSendCell {
    #[cfg(feature = "std")]
    inner: std::sync::Mutex<TypeHolderSend>,
    #[cfg(all(feature = "spin", not(feature = "std")))]
    inner: spin::mutex::Mutex<TypeHolderSend>,
}

impl TypeHolderSendCell {
    const fn new() -> Self {
        Self {
            #[cfg(feature = "std")]
            inner: std::sync::Mutex::new(TypeHolderSend::new()),
            #[cfg(all(feature = "spin", not(feature = "std")))]
            inner: spin::mutex::Mutex::new(TypeHolderSend::new()),
        }
    }

    fn get_mut(&self) -> impl DerefMut<Target = TypeHolderSend> + '_ {
        #[cfg(feature = "std")]
        return self
            .inner
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);

        #[cfg(all(feature = "spin", not(feature = "std")))]
        return self.inner.lock();
    }
}

pub struct Arena {
    containers: [TypeHolderSendCell; TYPE_BUCKETS],
}

impl Arena {
    pub const fn new() -> Self {
        #[allow(clippy::declare_interior_mutable_const)]
        const CONTAINER: TypeHolderSendCell = TypeHolderSendCell::new();
        Arena {
            containers: [CONTAINER; TYPE_BUCKETS],
        }
    }

    pub fn with<F, T, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
        T: Any + Send + Default,
    {
        f(self.containers[type_bucket::<T>()].get_mut().get_type_mut())
    }
}

#[test]
fn test_arena() {
    let arena = Arena::new();
    arena.with(|x: &mut i32| {
        *x = 42;
    });
    arena.with(|x: &mut u32| {
        *x = 137;
    });
    arena.with(|x: &mut i32| {
        assert_eq!(*x, 42);
    });
    arena.with(|x: &mut u32| {
        assert_eq!(*x, 137);
    });
}
