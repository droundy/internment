#![deny(missing_docs)]
use crate::boxedset::HashSet;
use alloc::{boxed::Box, string::String, vec::Vec};
use core::{
    borrow::Borrow,
    hash::{Hash, Hasher},
};

#[cfg(not(any(feature = "std", feature = "spin")))]
compile_error!(
    "Require either the `std` or spin `features` to be enabled when using the `arena` feature"
);

#[cfg(test)]
use std::println;

/// A arena for storing interned data
///
/// You can use an `Arena<T>` to intern data of type `T`.  This data is then
/// freed when the `Arena` is dropped.  An arena can hold some kinds of `!Sized`
/// data, such as `str`.
///
/// # Example
/// ```
/// let arena = internment::Arena::<str>::new();
/// // You can intern a `&str` object.
/// let x = arena.intern("world");
/// // You can also intern a `String`, in which case the data will not be copied
/// // if the value has not yet been interned.
/// let y = arena.intern_string(format!("hello {}", x));
/// // Interning a boxed `str` will also never require copying the data.
/// let v: Box<str> = "hello world".into();
/// let z = arena.intern_box(v);
/// // Any comparison of interned values will only need to check that the pointers
/// // are equal and will thus be fast.
/// assert_eq!(y, z);
/// assert!(x != z);
/// ```
///
/// # Another example
/// ```rust
/// use internment::Arena;
/// let arena: Arena<&'static str> = Arena::new();
/// let x = arena.intern("hello");
/// let y = arena.intern("world");
/// assert_ne!(x, y);
/// println!("The conventional greeting is '{} {}'", x, y);
/// ```

#[cfg_attr(docsrs, doc(cfg(feature = "arena")))]
pub struct Arena<T: ?Sized> {
    #[cfg(feature = "std")]
    data: std::sync::Mutex<HashSet<Box<T>>>,
    #[cfg(all(feature = "spin", not(feature = "std")))]
    data: spin::mutex::Mutex<HashSet<Box<T>>>,
}

impl<T: ?Sized> Arena<T> {
    fn get_mut(&self) -> impl core::ops::DerefMut<Target = HashSet<Box<T>>> + '_ {
        #[cfg(feature = "std")]
        return self
            .data
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);

        #[cfg(all(feature = "spin", not(feature = "std")))]
        return self.data.lock();
    }
}

#[cfg(feature = "deepsize")]
impl<T: ?Sized + deepsize::DeepSizeOf> deepsize::DeepSizeOf for Arena<T> {
    fn deep_size_of_children(&self, context: &mut deepsize::Context) -> usize {
        let hashset = self.get_mut();
        (*hashset).deep_size_of_children(context)
    }
}

/// An interned object reference with the data stored in an `Arena<T>`.
#[cfg_attr(docsrs, doc(cfg(feature = "arena")))]
pub struct ArenaIntern<'a, T: ?Sized> {
    pointer: &'a T,
}

#[cfg(feature = "deepsize")]
impl<T: ?Sized + deepsize::DeepSizeOf> deepsize::DeepSizeOf for ArenaIntern<'_, T> {
    fn deep_size_of_children(&self, _context: &mut deepsize::Context) -> usize {
        core::mem::size_of::<&T>()
    }
}

impl<T: ?Sized> Clone for ArenaIntern<'_, T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}
impl<T: ?Sized> Copy for ArenaIntern<'_, T> {}

impl<T: ?Sized> Arena<T> {
    /// Allocate a new `Arena`
    #[inline]
    pub fn new() -> Self {
        Arena {
            #[cfg(feature = "std")]
            data: std::sync::Mutex::new(HashSet::new()),
            #[cfg(all(feature = "spin", not(feature = "std")))]
            data: spin::mutex::Mutex::new(HashSet::new()),
        }
    }
}
impl<T: Eq + Hash + ?Sized> Arena<T> {
    /// Return the interned copy of `val`, first storing `into_box(val)` in the
    /// arena if no equal value is there yet.
    fn intern_with<Q, V>(&self, val: V, into_box: impl FnOnce(V) -> Box<T>) -> ArenaIntern<'_, T>
    where
        Q: Eq + Hash + ?Sized,
        T: Borrow<Q>,
        V: Borrow<Q>,
    {
        let mut m = self.get_mut();
        let p: *const T = if let Some(b) = m.get(val.borrow()) {
            &**b
        } else {
            let b = into_box(val);
            let p: *const T = &*b;
            m.insert(b);
            p
        };
        // SAFETY: the `Box` is never removed from the arena (so its contents
        // never move or get freed) until the arena itself is dropped, and the
        // returned `ArenaIntern` borrows the arena.
        ArenaIntern {
            pointer: unsafe { &*p },
        }
    }
}
impl<T: Eq + Hash> Arena<T> {
    /// Intern a value.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the object previously allocated.
    pub fn intern(&self, val: T) -> ArenaIntern<'_, T> {
        self.intern_with(val, Box::new)
    }
}
impl<T: Eq + Hash + ?Sized> Arena<T> {
    /// Tedst
    pub fn intern_ref<'a, 'b, I>(&'a self, val: &'b I) -> ArenaIntern<'a, T>
    where
        T: 'a + Borrow<I>,
        Box<T>: From<&'b I>,
        I: Eq + core::hash::Hash + ?Sized,
    {
        self.intern_with(val, Box::from)
    }
    fn intern_from_owned<I>(&self, val: I) -> ArenaIntern<'_, T>
    where
        Box<T>: From<I>,
        I: Borrow<T>,
    {
        self.intern_with(val, Box::from)
    }
}
impl Arena<str> {
    /// Intern a `&str` as `ArenaIntern<str>`.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the `str` previously allocated.
    #[inline]
    pub fn intern<'a>(&'a self, val: &str) -> ArenaIntern<'a, str> {
        self.intern_ref(val)
    }
    /// Intern a `String` as `ArenaIntern<str>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `String`.  Otherwise, it will free its input `String` and
    /// return a pointer to the `str` previously saved.
    #[inline]
    pub fn intern_string(&self, val: String) -> ArenaIntern<'_, str> {
        self.intern_from_owned(val)
    }
    /// Intern a `Box<str>` as `ArenaIntern<str>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `Box<str>`.  Otherwise, it will free its input `Box<str>`
    /// and return a pointer to the `str` previously saved.
    #[inline]
    pub fn intern_box(&self, val: Box<str>) -> ArenaIntern<'_, str> {
        self.intern_from_owned(val)
    }
}
impl Arena<core::ffi::CStr> {
    /// Intern a `&CStr` as `ArenaIntern<CStr>`.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the `CStr` previously allocated.
    ///
    /// # Example
    /// ```
    /// # use internment::Arena;
    /// # let arena = Arena::<std::ffi::CStr>::new();
    /// let x = arena.intern(std::ffi::CString::new("hello").unwrap().as_c_str());
    /// let y = arena.intern(std::ffi::CString::new("hello").unwrap().as_c_str());
    /// assert_eq!(x, y);
    /// ```
    #[inline]
    pub fn intern<'a>(&'a self, val: &core::ffi::CStr) -> ArenaIntern<'a, core::ffi::CStr> {
        self.intern_ref(val)
    }
    /// Intern a `CString` as `ArenaIntern<CStr>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `CString`.  Otherwise, it will free its input `CString` and
    /// return a pointer to the `CStr` previously saved.
    ///
    /// # Example
    /// ```
    /// # use internment::Arena;
    /// # let arena = Arena::<std::ffi::CStr>::new();
    /// let x = arena.intern_cstring(std::ffi::CString::new("hello").unwrap());
    /// let y = arena.intern_cstring(std::ffi::CString::new("hello").unwrap());
    /// assert_eq!(x, y);
    /// ```
    #[inline]
    pub fn intern_cstring(&self, val: alloc::ffi::CString) -> ArenaIntern<'_, core::ffi::CStr> {
        self.intern_from_owned(val)
    }
    /// Intern a `Box<CStr>` as `ArenaIntern<CStr>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `Box<CStr>`.  Otherwise, it will free its input `Box<CStr>`
    /// and return a pointer to the `CStr` previously saved.
    ///
    /// # Example
    /// ```
    /// # use internment::Arena;
    /// # let arena = Arena::<std::ffi::CStr>::new();
    /// let x = arena.intern_cstring(std::ffi::CString::new("hello").unwrap());
    /// let y = arena.intern_box(std::ffi::CString::new("hello").unwrap().into_boxed_c_str());
    /// assert_eq!(x, y);
    /// ```
    #[inline]
    pub fn intern_box(&self, val: Box<core::ffi::CStr>) -> ArenaIntern<'_, core::ffi::CStr> {
        self.intern_from_owned(val)
    }
}
#[cfg(feature = "std")]
impl Arena<std::ffi::OsStr> {
    /// Intern a `&OsStr` as `ArenaIntern<OsStr>`.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the `OsStr` previously allocated.
    ///
    /// # Example
    /// ```
    /// # use internment::Arena;
    /// # let arena = Arena::<std::ffi::OsStr>::new();
    /// let x = arena.intern(std::ffi::OsStr::new("hello"));
    /// let y = arena.intern(std::ffi::OsStr::new("hello"));
    /// assert_eq!(x, y);
    /// ```
    #[inline]
    pub fn intern<'a>(&'a self, val: &std::ffi::OsStr) -> ArenaIntern<'a, std::ffi::OsStr> {
        self.intern_ref(val)
    }
    /// Intern a `OsString` as `ArenaIntern<OsStr>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `OsString`.  Otherwise, it will free its input `OsString` and
    /// return a pointer to the `OsStr` previously saved.
    ///
    /// # Example
    /// ```
    /// # use internment::Arena;
    /// # let arena = Arena::<std::ffi::OsStr>::new();
    /// let x = arena.intern_osstring(std::ffi::OsString::from("hello"));
    /// let y = arena.intern_osstring(std::ffi::OsString::from("hello"));
    /// assert_eq!(x, y);
    /// ```
    #[inline]
    pub fn intern_osstring(&self, val: std::ffi::OsString) -> ArenaIntern<'_, std::ffi::OsStr> {
        self.intern_from_owned(val)
    }
    /// Intern a `Box<OsStr>` as `ArenaIntern<OsStr>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `Box<OsStr>`.  Otherwise, it will free its input `Box<OsStr>`
    /// and return a pointer to the `OsStr` previously saved.
    ///
    /// # Example
    /// ```
    /// # use internment::Arena;
    /// # let arena = Arena::<std::ffi::OsStr>::new();
    /// let x = arena.intern_osstring(std::ffi::OsString::from("hello"));
    /// let y = arena.intern_box(std::ffi::OsString::from("hello").into_boxed_os_str());
    /// assert_eq!(x, y);
    /// ```
    #[inline]
    pub fn intern_box(&self, val: Box<std::ffi::OsStr>) -> ArenaIntern<'_, std::ffi::OsStr> {
        self.intern_from_owned(val)
    }
}
#[cfg(feature = "std")]
impl Arena<std::path::Path> {
    /// Intern a `&Path` as `ArenaIntern<Path>`.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the `Path` previously allocated.
    ///
    /// # Example
    /// ```
    /// # use internment::Arena;
    /// # let arena = Arena::<std::path::Path>::new();
    /// let x = arena.intern(std::path::Path::new("hello"));
    /// let y = arena.intern(std::path::Path::new("hello"));
    /// assert_eq!(x, y);
    /// ```
    #[inline]
    pub fn intern<'a>(&'a self, val: &std::path::Path) -> ArenaIntern<'a, std::path::Path> {
        self.intern_ref(val)
    }
    /// Intern a `PathBuf` as `ArenaIntern<Path>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `PathBuf`.  Otherwise, it will free its input `PathBuf` and
    /// return a pointer to the `Path` previously saved.
    ///
    /// # Example
    /// ```
    /// # use internment::Arena;
    /// # let arena = Arena::<std::path::Path>::new();
    /// let x = arena.intern_pathbuf(std::path::PathBuf::from("hello"));
    /// let y = arena.intern_pathbuf(std::path::PathBuf::from("hello"));
    /// assert_eq!(x, y);
    /// ```
    #[inline]
    pub fn intern_pathbuf(&self, val: std::path::PathBuf) -> ArenaIntern<'_, std::path::Path> {
        self.intern_from_owned(val)
    }
    /// Intern a `Box<Path>` as `ArenaIntern<Path>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `Box<Path>`.  Otherwise, it will free its input `Box<Path>`
    /// and return a pointer to the `Path` previously saved.
    ///
    /// # Example
    /// ```
    /// # use internment::Arena;
    /// # let arena = Arena::<std::path::Path>::new();
    /// let x = arena.intern_pathbuf(std::path::PathBuf::from("hello"));
    /// let y = arena.intern_box(std::path::PathBuf::from("hello").into_boxed_path());
    /// assert_eq!(x, y);
    /// ```
    #[inline]
    pub fn intern_box(&self, val: Box<std::path::Path>) -> ArenaIntern<'_, std::path::Path> {
        self.intern_from_owned(val)
    }
}
impl<T: Eq + Hash + Copy> Arena<[T]> {
    /// Intern a `&[T]` as `ArenaIntern<[T]>`.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the `[T]` previously allocated.
    #[inline]
    pub fn intern<'a>(&'a self, val: &[T]) -> ArenaIntern<'a, [T]> {
        self.intern_ref(val)
    }
    /// Intern a `Vec<T>` as `ArenaIntern<[T]>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `Vec<T>`.  Otherwise, it will free its input `Vec<T>` and
    /// return a pointer to the `[T]` previously saved.
    #[inline]
    pub fn intern_vec(&self, val: Vec<T>) -> ArenaIntern<'_, [T]> {
        self.intern_from_owned(val)
    }
    /// Intern a `Box<[T]>` as `ArenaIntern<[T]>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `Box<CSr>`.  Otherwise, it will free its input `Box<[T]>`
    /// and return a pointer to the `[T]` previously saved.
    #[inline]
    pub fn intern_box(&self, val: Box<[T]>) -> ArenaIntern<'_, [T]> {
        self.intern_from_owned(val)
    }
}
impl<T: Eq + Hash + ?Sized> Arena<T> {
    /// Intern a reference to a type that can be converted into a `Box<T>` as `ArenaIntern<T>`.
    pub fn intern_from<'a, 'b, I>(&'a self, val: &'b I) -> ArenaIntern<'a, T>
    where
        T: 'a + Borrow<I> + From<&'b I>,
        I: Eq + core::hash::Hash + ?Sized,
    {
        self.intern_with(val, |val| Box::new(T::from(val)))
    }
}

impl<T> Default for Arena<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: ?Sized> AsRef<T> for ArenaIntern<'_, T> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        self.pointer
    }
}

impl<T: ?Sized> core::ops::Deref for ArenaIntern<'_, T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'a, T: ?Sized> ArenaIntern<'a, T> {
    #[inline(always)]
    fn get_pointer(&self) -> *const T {
        self.pointer as *const T
    }

    /// Get a reference to a value interned into an arena.
    ///
    /// This function allows you to store values into a structure
    /// inline, without having to take a `&'a` reference to an
    /// `ArenaIntern<'a, T>`. This is required as using
    /// [`std::ops::Deref`] or [`std::convert::AsRef`]
    /// requires a `&self` receiver, but doing so, due to the bounds
    /// of these traits' functions, would implicitly require that
    /// this reference lives for `'a`.
    ///
    /// # Example
    ///
    /// Consider the following structures.
    /// ```rust
    /// # use internment::ArenaIntern;
    /// struct Bar {
    ///     baz: String,
    /// }
    ///
    /// struct Foo<'a>(ArenaIntern<'a, Bar>);
    /// ```
    ///
    /// The following code does not compile.
    /// ```compile_fail
    /// # use internment::ArenaIntern;
    /// # struct Bar {
    /// #     baz: String,
    /// # }
    /// #
    /// # struct Foo<'a>(ArenaIntern<'a, Bar>);
    /// #
    /// impl<'a> Foo<'a> {
    ///     pub fn get_baz(self) -> &'a str {
    ///         &self.0.as_ref().baz
    ///         // ^^^ ERROR: cannot return value referencing local data `self.0`
    ///     }
    /// }
    /// ```
    ///
    /// This similar code, which uses `into_ref`, does compile.
    /// ```rust
    /// # use internment::ArenaIntern;
    /// # struct Bar {
    /// #     baz: String,
    /// # }
    /// #
    /// # struct Foo<'a>(ArenaIntern<'a, Bar>);
    /// #
    /// impl<'a> Foo<'a> {
    ///     pub fn get_baz(self) -> &'a str {
    ///         &self.0.into_ref().baz
    ///     }
    /// }
    /// ```
    #[inline(always)]
    pub fn into_ref(self) -> &'a T {
        self.pointer
    }
}

/// The hash implementation returns the hash of the pointer
/// value, not the hash of the value pointed to.  This should
/// be irrelevant, since there is a unique pointer for every
/// value, but it *is* observable, since you could compare the
/// hash of the pointer with hash of the data itself.
impl<T: ?Sized> Hash for ArenaIntern<'_, T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_pointer().hash(state);
    }
}

impl<T: ?Sized> PartialEq for ArenaIntern<'_, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        core::ptr::eq(self.get_pointer(), other.get_pointer())
    }
}
impl<T: ?Sized> Eq for ArenaIntern<'_, T> {}

// #[cfg(feature = "arena")]
// create_impls_no_new!(ArenaIntern, arenaintern_impl_tests, ['a], [Eq, Hash], [Eq, Hash]);

impl<T: core::fmt::Debug + ?Sized> core::fmt::Debug for ArenaIntern<'_, T> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
        self.as_ref().fmt(f)
    }
}

impl<T: core::fmt::Display + ?Sized> core::fmt::Display for ArenaIntern<'_, T> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
        self.as_ref().fmt(f)
    }
}

#[test]
fn eq_string() {
    let arena = Arena::<&'static str>::new();
    assert_eq!(arena.intern("hello"), arena.intern("hello"));
    assert_ne!(arena.intern("goodbye"), arena.intern("farewell"));
}
#[test]
fn display() {
    let arena = Arena::<&'static str>::new();
    let world = arena.intern("world");
    println!("Hello {}", world);
}
#[test]
fn debug() {
    let arena = Arena::<&'static str>::new();
    let world = arena.intern("world");
    println!("Hello {:?}", world);
}
#[test]
fn can_clone() {
    let arena = Arena::<&'static str>::new();
    assert_eq!(arena.intern("hello").clone(), arena.intern("hello"));
}
#[test]
fn has_deref() {
    let arena = Arena::<Option<String>>::new();
    let x = arena.intern(None);
    let b: &Option<String> = x.as_ref();
    use core::ops::Deref;
    assert_eq!(b, arena.intern(None).deref());
}

#[test]
fn unsized_str() {
    let arena = Arena::<str>::new();
    let x = arena.intern("hello");
    let b: &str = x.as_ref();
    assert_eq!("hello", b);
}

#[test]
fn ref_to_string() {
    let arena = Arena::<String>::new();
    let x = arena.intern_from("hello");
    assert_eq!("hello", &*x);
}

#[test]
fn str_from_owned_and_boxed() {
    let arena = Arena::<str>::new();
    let borrowed = arena.intern("hello");
    // The owned and boxed versions are the same value, so the same interned data.
    assert_eq!(borrowed, arena.intern_string(String::from("hello")));
    assert_eq!(borrowed, arena.intern_box(Box::<str>::from("hello")));
    assert_ne!(borrowed, arena.intern_string(String::from("world")));
    assert_ne!(borrowed, arena.intern_box(Box::<str>::from("world")));
}

#[test]
fn cstr_from_borrowed_owned_and_boxed() {
    use alloc::ffi::CString;
    use core::ffi::CStr;
    let arena = Arena::<CStr>::new();
    let borrowed = arena.intern(CStr::from_bytes_with_nul(b"hello\0").unwrap());
    assert_eq!(
        borrowed,
        arena.intern_cstring(CString::new("hello").unwrap())
    );
    assert_eq!(
        borrowed,
        arena.intern_box(CString::new("hello").unwrap().into_boxed_c_str())
    );
    assert_ne!(
        borrowed,
        arena.intern_cstring(CString::new("world").unwrap())
    );
    assert_ne!(
        borrowed,
        arena.intern_box(CString::new("world").unwrap().into_boxed_c_str())
    );
}

#[cfg(feature = "std")]
#[test]
fn osstr_from_borrowed_owned_and_boxed() {
    use std::ffi::{OsStr, OsString};
    let arena = Arena::<OsStr>::new();
    let borrowed = arena.intern(OsStr::new("hello"));
    assert_eq!(borrowed, arena.intern_osstring(OsString::from("hello")));
    assert_eq!(
        borrowed,
        arena.intern_box(OsString::from("hello").into_boxed_os_str())
    );
    assert_ne!(borrowed, arena.intern_osstring(OsString::from("world")));
    assert_ne!(
        borrowed,
        arena.intern_box(OsString::from("world").into_boxed_os_str())
    );
}

#[cfg(feature = "std")]
#[test]
fn path_from_borrowed_owned_and_boxed() {
    use std::path::{Path, PathBuf};
    let arena = Arena::<Path>::new();
    let borrowed = arena.intern(Path::new("a/b"));
    assert_eq!(borrowed, arena.intern_pathbuf(PathBuf::from("a/b")));
    assert_eq!(
        borrowed,
        arena.intern_box(PathBuf::from("a/b").into_boxed_path())
    );
    assert_ne!(borrowed, arena.intern_pathbuf(PathBuf::from("a/c")));
    assert_ne!(
        borrowed,
        arena.intern_box(PathBuf::from("a/c").into_boxed_path())
    );
}

#[test]
fn slice_from_borrowed_owned_and_boxed() {
    use alloc::vec;
    let arena = Arena::<[u8]>::new();
    let borrowed = arena.intern(&[1, 2, 3][..]);
    assert_eq!(borrowed, arena.intern_vec(vec![1, 2, 3]));
    assert_eq!(borrowed, arena.intern_box(vec![1, 2, 3].into_boxed_slice()));
    assert_ne!(borrowed, arena.intern_vec(vec![1, 2, 4]));
    assert_ne!(borrowed, arena.intern_box(vec![1, 2, 4].into_boxed_slice()));
}

#[test]
fn intern_ref_matches_intern() {
    let arena = Arena::<str>::new();
    let borrowed = arena.intern("hello");
    assert_eq!(borrowed, arena.intern_ref("hello"));
}
