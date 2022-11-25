#![deny(missing_docs)]

use std::{
    borrow::{Borrow, Cow},
    hash::Hash,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use dashmap::mapref::entry::Entry;
#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer};

use super::arc::{ArcIntern, BoxRefCount, RefCount};

impl<T: Copy> RefCount<[T]> {
    fn from_slice(slice: &[T]) -> Box<RefCount<[T]>> {
        use std::alloc::Layout;
        let layout = Layout::new::<RefCount<()>>()
            .extend(Layout::array::<T>(slice.len()).unwrap())
            .unwrap()
            .0
            .pad_to_align();
        // SAFETY: the layout is not zero-sized, it at least has an `AtomicUsize`.
        let ptr = unsafe { std::alloc::alloc(layout) };
        // imitate the `std::Arc::new_zeroed_slice` and `std::Arc::try_allocate_for_layout`.
        let ptr =
            std::ptr::slice_from_raw_parts_mut(ptr as *mut T, slice.len()) as *mut RefCount<[T]>;

        unsafe {
            // SAFETY: the ptr is allocated by the global allocator with proper layout, as per the
            // [Memory Layout](https://doc.rust-lang.org/stable/std/boxed/index.html#memory-layout) section
            // of [`std::boxed`].
            let mut this = Box::from_raw(ptr);

            std::ptr::write(&mut this.count, AtomicUsize::new(1));

            // SAFETY: valid for reads, writes, aligned and not overlapped.
            // and T is Copy, so don't worry about drop.
            let dst = &mut this.data as *mut [T] as *mut T;
            std::ptr::copy_nonoverlapping(slice.as_ptr(), dst, slice.len());
            this
        }
    }
}

impl RefCount<str> {
    fn from_str(s: &str) -> Box<RefCount<str>> {
        let bytes = s.as_bytes();
        let boxed_refcount = RefCount::<[u8]>::from_slice(bytes);
        debug_assert_eq!(s.len(), boxed_refcount.data.len());

        // SAFETY: str and [u8] have the same memory layout.
        unsafe { Box::from_raw(Box::into_raw(boxed_refcount) as *mut RefCount<str>) }
    }
}

impl<T: ?Sized + Eq + Hash + Send + Sync + 'static> ArcIntern<T> {
    /// make new [`ArcIntern`] with copyable initial value, like `&str` or `&[u8]`.
    fn new_with_copyable_init_val<I, NewFn>(val: &I, new_fn: NewFn) -> ArcIntern<T>
    where
        I: ?Sized + Hash + std::cmp::Eq,
        BoxRefCount<T>: Borrow<I>,
        NewFn: Fn(&I) -> Box<RefCount<T>>,
    {
        // cache the converted BoxRefCount to avoid copy. This only takes an usize.
        let mut converted = None;
        loop {
            let m = Self::get_container();

            if let Some(b) = m.get_mut(val) {
                let b = b.key();
                // First increment the count.  We are holding the write mutex here.
                // Has to be the write mutex to avoid a race
                let oldval = b.0.count.fetch_add(1, Ordering::SeqCst);
                if oldval != 0 {
                    // we can only use this value if the value is not about to be freed
                    return ArcIntern {
                        pointer: std::ptr::NonNull::from(b.0.borrow()),
                    };
                } else {
                    // we have encountered a race condition here.
                    // we will just wait for the object to finish
                    // being freed.
                    b.0.count.fetch_sub(1, Ordering::SeqCst);
                }
            } else {
                let b = std::mem::take(&mut converted).unwrap_or_else(|| new_fn(val));
                match m.entry(BoxRefCount(b)) {
                    Entry::Vacant(e) => {
                        // We can insert, all is good
                        let p = ArcIntern {
                            pointer: std::ptr::NonNull::from(e.key().0.borrow()),
                        };
                        e.insert(());
                        return p;
                    }
                    Entry::Occupied(e) => {
                        // Race, map already has data, go round again
                        let box_ref_count = e.into_key();
                        converted = Some(box_ref_count.0);
                    }
                }
            }
            // yield so that the object can finish being freed,
            // and then we will be able to intern a new copy.
            std::thread::yield_now();
        }
    }
}

impl From<&str> for ArcIntern<str> {
    fn from(s: &str) -> Self {
        ArcIntern::<str>::new_with_copyable_init_val(s, |s| RefCount::<str>::from_str(s))
    }
}

macro_rules! impl_from {
    ([$($vars:tt)*] $from:ty, $to:ty) => {
        #[allow(unused_lifetimes)]
        impl<'a, $($vars)*> From<$from> for $to {
            fn from(f: $from) -> Self {
                Self::from(&f[..])
            }
        }
    };
}
impl_from! { [] String, ArcIntern<str> }
impl_from! { [] Box<str>, ArcIntern<str> }
impl_from! { [] Arc<str>, ArcIntern<str> }
impl_from! { [] std::rc::Rc<str>, ArcIntern<str> }
impl<'a, B> From<Cow<'a, B>> for ArcIntern<B>
where
    B: ToOwned + ?Sized + Send + Sync + Hash + Eq,
    ArcIntern<B>: From<&'a B>,
    ArcIntern<B>: From<<B as ToOwned>::Owned>,
{
    fn from(c: Cow<'a, B>) -> Self {
        match c {
            Cow::Borrowed(b) => b.into(),
            Cow::Owned(o) => o.into(),
        }
    }
}

impl<T> From<&[T]> for ArcIntern<[T]>
where
    T: Copy + Send + Sync + Hash + Eq + 'static,
{
    fn from(slice: &[T]) -> Self {
        ArcIntern::<[T]>::new_with_copyable_init_val(slice, |slice| {
            RefCount::<[T]>::from_slice(slice)
        })
    }
}
impl_from! { [T: Copy + Send + Sync + Hash + Eq + 'static] Vec<T>, ArcIntern<[T]> }
impl_from! { [T: Copy + Send + Sync + Hash + Eq + 'static] Box<[T]>, ArcIntern<[T]> }
impl_from! { [T: Copy + Send + Sync + Hash + Eq + 'static] Arc<[T]>, ArcIntern<[T]> }
impl_from! { [T: Copy + Send + Sync + Hash + Eq + 'static] std::rc::Rc<[T]>, ArcIntern<[T]> }

impl Default for ArcIntern<str> {
    fn default() -> Self {
        Self::from("")
    }
}
impl<T> Default for ArcIntern<[T]>
where
    T: Copy + Send + Sync + Hash + Eq + 'static,
{
    fn default() -> Self {
        Self::from(&[][..])
    }
}

// implement some useful equal comparisons
macro_rules! impl_eq {
    ([$($vars:tt)*] $lhs:ty, $rhs: ty) => {
        #[allow(unused_lifetimes)]
        impl<'a, $($vars)*> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool {
                PartialEq::ne(&self[..], &other[..])
            }
        }

        #[allow(unused_lifetimes)]
        impl<'a, $($vars)*> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$lhs) -> bool {
                PartialEq::ne(&self[..], &other[..])
            }
        }
    };
}
impl_eq! { [] ArcIntern<str>, str }
impl_eq! { [] ArcIntern<str>, &'a str }
impl_eq! { [] ArcIntern<str>, String }
impl_eq! { [] ArcIntern<str>, std::borrow::Cow<'a, str> }
impl_eq! { [] ArcIntern<str>, Box<str> }
impl_eq! { [] ArcIntern<str>, std::rc::Rc<str> }
impl_eq! { [] ArcIntern<str>, std::sync::Arc<str> }
impl_eq! { [T: Copy + Send + Sync + Hash + Eq + 'static] ArcIntern<[T]>, Vec<T> }
impl_eq! { [T: Copy + Send + Sync + Hash + Eq + 'static] ArcIntern<[T]>, [T] }
impl_eq! { [T: Copy + Send + Sync + Hash + Eq + 'static] ArcIntern<[T]>, &'a [T] }
impl_eq! { [T: Copy + Send + Sync + Hash + Eq + 'static] ArcIntern<[T]>, &'a mut [T] }
impl_eq! { [T: Copy + Send + Sync + Hash + Eq + 'static] ArcIntern<[T]>, std::borrow::Cow<'a, [T]> }
impl_eq! { [T: Copy + Send + Sync + Hash + Eq + 'static] ArcIntern<[T]>, Box<[T]> }
impl_eq! { [T: Copy + Send + Sync + Hash + Eq + 'static] ArcIntern<[T]>, std::rc::Rc<[T]> }
impl_eq! { [T: Copy + Send + Sync + Hash + Eq + 'static] ArcIntern<[T]>, std::sync::Arc<[T]> }
impl_eq! { [T: Copy + Send + Sync + Hash + Eq + 'static, const N: usize] ArcIntern<[T]>, [T; N] }
impl_eq! { [T: Copy + Send + Sync + Hash + Eq + 'static, const N: usize] ArcIntern<[T]>, &[T; N] }

/// Deserialize into `&'a str` will fail to parse escaped string,
/// deserialize into `String` will cause unnecessary copy.
/// We implement a new visitor to get as less copy as possible for deserialization.
#[cfg(feature = "serde")]
struct StrVisitor;
#[cfg(feature = "serde")]
impl<'a> serde::de::Visitor<'a> for StrVisitor {
    type Value = ArcIntern<str>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a borrowed or owned string")
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(ArcIntern::from(v))
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(ArcIntern::from(v))
    }
}
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
#[cfg(feature = "serde")]
impl<'de: 'a, 'a> Deserialize<'de> for ArcIntern<str> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_str(StrVisitor)
    }
}

#[cfg(feature = "serde")]
struct BytesVisitor;
#[cfg(feature = "serde")]
impl<'a> serde::de::Visitor<'a> for BytesVisitor {
    type Value = ArcIntern<[u8]>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a borrowed or owned byte array")
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(ArcIntern::from(v))
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(ArcIntern::from(v))
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
#[cfg(feature = "serde")]
impl<'de: 'a, 'a> Deserialize<'de> for ArcIntern<[u8]> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_bytes(BytesVisitor)
    }
}

#[test]
fn dst_arc_intern_is_sized() {
    struct _Assure
    where
        ArcIntern<str>: Sized;
    struct _Assure2
    where
        ArcIntern<[u8]>: Sized;
}

#[test]
fn dst_arc_intern_is_hash() {
    struct _Assure
    where
        ArcIntern<str>: Hash;
}

#[test]
fn dst_arc_intern_is_clone() {
    struct _Assure
    where
        ArcIntern<str>: Clone;
}

#[test]
fn dst_arc_intern_is_borrow() {
    // demonstrate that Arc has this ability
    let map = std::collections::HashMap::<std::sync::Arc<str>, u32>::new();
    assert!(map.get("dst_arc_intern_is_borrow").is_none());

    let map = std::collections::HashMap::<ArcIntern<str>, u32>::new();
    assert!(map.get("dst_arc_intern_is_borrow").is_none());
}

#[test]
fn dst_arc_intern_is_send_and_sync() {
    struct _Assure
    where
        ArcIntern<str>: Send + Sync;
}

#[test]
fn common_equal_comparisons() {
    let s1: ArcIntern<str> = ArcIntern::from("common_equal_comparisons");
    let s2: &str = "common_equal_comparisons";
    let s3: String = "common_equal_comparisons".to_string();
    let s4: std::borrow::Cow<'_, str> = "common_equal_comparisons".into();
    let s5: Box<str> = "common_equal_comparisons".into();
    let s6: std::rc::Rc<str> = "common_equal_comparisons".into();
    let s7: std::sync::Arc<str> = "common_equal_comparisons".into();
    assert_eq!(s1, s2);
    assert_eq!(s1, s3);
    assert_eq!(s1, s4);
    assert_eq!(s1, s5);
    assert_eq!(s1, s6);
    assert_eq!(s1, s7);
}

#[test]
fn common_from_conversions() {
    let s1: ArcIntern<str> = ArcIntern::from("common_from_conversions");
    let s2: &str = "common_from_conversions";
    let s3: String = "common_from_conversions".to_string();
    let s4: std::borrow::Cow<'_, str> = "common_from_conversions".into();
    let s5: Box<str> = "common_from_conversions".into();
    let s6: std::rc::Rc<str> = "common_from_conversions".into();
    let s7: std::sync::Arc<str> = "common_from_conversions".into();
    assert_eq!(ArcIntern::from(s2), s1);
    assert_eq!(ArcIntern::from(s3), s1);
    assert_eq!(ArcIntern::from(s4), s1);
    assert_eq!(ArcIntern::from(s5), s1);
    assert_eq!(ArcIntern::from(s6), s1);
    assert_eq!(ArcIntern::from(s7), s1);
}

#[cfg(feature = "serde")]
#[test]
fn deserialize_arc_intern_str() {
    let s = "\"a\"";
    let mut deserializer = serde_json::Deserializer::from_str(s);
    let s = <ArcIntern<str> as serde::Deserialize>::deserialize(&mut deserializer).unwrap();
    assert_eq!(s, "a");
    assert_eq!("a", s);

    // escaped
    let s = "\"a\\nb\"";
    let mut deserializer = serde_json::Deserializer::from_str(s);
    let s = <ArcIntern<str> as serde::Deserialize>::deserialize(&mut deserializer).unwrap();
    assert_eq!(s, "a\nb");
}

#[cfg(feature = "serde")]
#[test]
fn serialize_arc_intern_str() {
    let s = ArcIntern::<str>::from("a");
    let s = serde_json::to_string(&s).unwrap();
    assert_eq!(s, "\"a\"");
}

#[test]
fn arc_intern_str() {
    let x: ArcIntern<str> = ArcIntern::from("hello");
    assert_eq!(x.len(), 5);
    assert_eq!(x.refcount(), 1);

    let y: ArcIntern<str> = ArcIntern::from("hello");
    assert_eq!(x.refcount(), 2);
    assert_eq!(y.refcount(), 2);

    assert_eq!(x.as_ptr(), y.as_ptr());
    assert_eq!(x, y);

    let z: ArcIntern<str> = ArcIntern::from(String::from("hello"));
    assert_eq!(x.refcount(), 3);
    assert_eq!(y.refcount(), 3);
    assert_eq!(z.refcount(), 3);

    std::mem::drop(x);
    assert_eq!(y.refcount(), 2);
    assert_eq!(z.refcount(), 2);
    std::mem::drop(y);
    assert_eq!(z.refcount(), 1);
}

#[test]
fn arc_intern_str_empty() {
    let x = ArcIntern::<str>::from("");
    assert_eq!(x.len(), 0);
    assert_eq!(x.refcount(), 1);
    assert_eq!(x, "");
}

#[test]
fn zst_for_dst() {
    let vec = vec![(); 500];
    let x: ArcIntern<[()]> = ArcIntern::from(vec.clone());
    assert_eq!(x.len(), 500);
    assert_eq!(x.refcount(), 1);

    let y: ArcIntern<[()]> = ArcIntern::from(vec);
    assert_eq!(x.refcount(), 2);
    assert_eq!(y.refcount(), 2);

    assert_eq!(x, y);
}

#[test]
fn dst_memory_aligned() {
    macro_rules! test_align {
        ($align:literal) => {{
            #[repr(align($align))]
            #[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
            struct Aligned(u8);

            // [The size of a value is always a multiple of its alignment](https://doc.rust-lang.org/reference/type-layout.html)
            assert_eq!(std::mem::align_of::<Aligned>(), $align);
            assert_eq!(std::mem::size_of::<Aligned>(), $align);

            let x: ArcIntern<[Aligned]> = ArcIntern::from(&[Aligned::default(); 10][..]);
            let ptr = unsafe { &*x.pointer.as_ptr() };
            // Arrays are laid out so that the zero-based nth element of the array is
            // offset from the start of the array by n * size_of::<T>() bytes.
            let addr0 = &ptr.data as *const [Aligned] as *const Aligned as usize;
            assert_eq!(addr0 % $align, 0);
            for idx in 1..10 {
                let addr_offset = &ptr.data[idx] as *const _ as usize;
                assert_eq!(addr0 + idx * std::mem::size_of::<Aligned>(), addr_offset);
            }

        }};
    }

    test_align!(1);
    test_align!(2);
    test_align!(4);
    test_align!(8);
    test_align!(16);
    test_align!(32);
    test_align!(64);
    test_align!(128);
    test_align!(256);
    test_align!(512);
    test_align!(1024);
    test_align!(2048);
    test_align!(4096);
}
