//! Spreading per-type containers over a fixed number of buckets.
//!
//! The interners keep one container per interned type, found by `TypeId`.  To
//! avoid searching every type's container, they are spread over
//! [`TYPE_BUCKETS`] buckets, and [`type_bucket`] says which one a type is in.

use core::any::TypeId;
use core::hash::{Hash, Hasher};

/// How many buckets the per-type containers are spread over.
pub(crate) const TYPE_BUCKETS: usize = 32;

/// Which of the [`TYPE_BUCKETS`] buckets holds the container for `T`.
#[inline]
pub(crate) fn type_bucket<T: 'static>() -> usize {
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
    hasher.finish() as usize % TYPE_BUCKETS
}

#[test]
fn same_type_same_bucket() {
    assert_eq!(type_bucket::<u32>(), type_bucket::<u32>());
    assert!(type_bucket::<u32>() < TYPE_BUCKETS);
    assert!(type_bucket::<alloc::string::String>() < TYPE_BUCKETS);
}
