use alloc::boxed::Box;
use append_only_vec::AppendOnlyVec;
use core::{
    any::{Any, TypeId},
    hash::{Hash, Hasher},
};

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

const INTERN_CONTAINER_COUNT: usize = 32;
pub struct Arena {
    containers: [TypeHolderSync; INTERN_CONTAINER_COUNT],
}

impl Arena {
    pub const fn new() -> Self {
        #[allow(clippy::declare_interior_mutable_const)]
        const CONTAINER: TypeHolderSync = TypeHolderSync::new();
        Arena {
            containers: [CONTAINER; INTERN_CONTAINER_COUNT],
        }
    }

    pub fn get<T>(&self) -> &T
    where
        T: Any + Send + Sync + Default,
    {
        // Compute the hash of the type.
        fn hash_of_type<T: 'static>() -> u64 {
            // We use very simple hasher, because it is optimized away to a constant:
            // https://rust.godbolt.org/z/4T1fa4GGs
            // which is not true for using `DefaultHasher`:
            // https://rust.godbolt.org/z/qKar1WKfz
            struct HasherForTypeId {
                hash: u64,
            }

            impl Hasher for HasherForTypeId {
                fn write(&mut self, bytes: &[u8]) {
                    // Hash for type only calls `write_u64` once,
                    // but handle this case explicitly to make sure
                    // this code doesn't break if stdlib internals change.

                    for byte in bytes {
                        self.hash = self.hash.wrapping_mul(31).wrapping_add(*byte as u64);
                    }
                }

                fn write_u64(&mut self, v: u64) {
                    self.hash = v;
                }

                fn finish(&self) -> u64 {
                    self.hash
                }
            }

            let mut hasher = HasherForTypeId { hash: 0 };
            TypeId::of::<T>().hash(&mut hasher);
            hasher.finish()
        }

        self.containers[hash_of_type::<T>() as usize % INTERN_CONTAINER_COUNT].get_type()
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
