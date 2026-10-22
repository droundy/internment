use crate::type_bucket::{type_bucket, TYPE_BUCKETS};
use alloc::boxed::Box;
use append_only_vec::AppendOnlyVec;
use core::any::Any;

#[cfg(not(any(feature = "std", feature = "spin")))]
compile_error!(
    "Require either the `std` or spin `features` to be enabled when using the `intern` feature"
);

pub struct TypeHolderSync(AppendOnlyVec<AnySend>);

struct AnySend(Box<dyn Any + Send + Sync>);

impl TypeHolderSync {
    pub fn get_type<T: Any + Send + Sync + Default>(&self) -> &T {
        if let Some(v) = self.0.iter().filter_map(|x| x.0.downcast_ref::<T>()).next() {
            v
        } else {
            let v: T = Default::default();
            let i = self.0.push(AnySend(Box::new(v)));
            self.0[i].0.downcast_ref().unwrap()
        }
    }
    pub const fn new() -> Self {
        TypeHolderSync(AppendOnlyVec::new())
    }
}

pub struct Arena {
    containers: [TypeHolderSync; TYPE_BUCKETS],
}

impl Arena {
    pub const fn new() -> Self {
        #[allow(clippy::declare_interior_mutable_const)]
        const CONTAINER: TypeHolderSync = TypeHolderSync::new();
        Arena {
            containers: [CONTAINER; TYPE_BUCKETS],
        }
    }

    pub fn get<T>(&self) -> &T
    where
        T: Any + Send + Sync + Default,
    {
        self.containers[type_bucket::<T>()].get_type()
    }
}

#[test]
fn test_arena() {
    let arena = Arena::new();
    let v1: &AppendOnlyVec<i32> = arena.get();
    let v2: &AppendOnlyVec<i64> = arena.get();
    let v3: &AppendOnlyVec<i32> = arena.get();
    assert_eq!(
        v1 as *const AppendOnlyVec<i32> as usize,
        v3 as *const AppendOnlyVec<i32> as usize
    );
    assert!(v1 as *const AppendOnlyVec<i32> as usize != v2 as *const AppendOnlyVec<i64> as usize);
}
