use parking_lot::Mutex;
use std::any::Any;
use std::any::TypeId;
use std::hash::{Hash, Hasher};

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

const INTERN_CONTAINER_COUNT: usize = 32;
pub struct Arena {
    containers: [Mutex<TypeHolderSend>; INTERN_CONTAINER_COUNT],
}

impl Arena {
    pub const fn new() -> Self {
        const EMPTY: Mutex<TypeHolderSend> = parking_lot::const_mutex(TypeHolderSend::new());
        Arena {
            containers: [EMPTY; INTERN_CONTAINER_COUNT],
        }
    }

    pub fn with<F, T, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
        T: Any + Send + Default,
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
            hasher.hash
        }

        f(
            self.containers[hash_of_type::<T>() as usize % INTERN_CONTAINER_COUNT]
                .lock()
                .get_type_mut(),
        )
    }
}
