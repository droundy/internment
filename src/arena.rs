#![deny(missing_docs)]
use crate::boxedset::HashSet;
use parking_lot::Mutex;
use std::borrow::Borrow;
use std::hash::{Hash, Hasher};

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
    data: Mutex<HashSet<Box<T>>>,
}
/// An interned object reference with the data stored in an `Arena<T>`.
#[cfg_attr(docsrs, doc(cfg(feature = "arena")))]
pub struct ArenaIntern<'a, T: ?Sized> {
    pointer: &'a T,
}

impl<'a, T: ?Sized> Clone for ArenaIntern<'a, T> {
    fn clone(&self) -> Self {
        ArenaIntern {
            pointer: self.pointer,
        }
    }
}
impl<'a, T: ?Sized> Copy for ArenaIntern<'a, T> {}

impl<T: ?Sized> Arena<T> {
    /// Allocate a new `Arena`
    pub fn new() -> Self {
        Arena {
            data: Mutex::new(HashSet::new()),
        }
    }
}
impl<T: Eq + Hash> Arena<T> {
    /// Intern a value.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the object previously allocated.
    pub fn intern(&self, val: T) -> ArenaIntern<T> {
        let mut m = self.data.lock();
        if let Some(b) = m.get(&val) {
            let p = b.as_ref() as *const T;
            return ArenaIntern {
                pointer: unsafe { &*p },
            };
        }
        let b = Box::new(val);
        let p = b.as_ref() as *const T;
        m.insert(b);
        ArenaIntern {
            pointer: unsafe { &*p },
        }
    }
}
impl<T: Eq + Hash + ?Sized> Arena<T> {
    /// Tedst
    pub fn intern_ref<'a, 'b, I>(&'a self, val: &'b I) -> ArenaIntern<'a, T>
    where
        T: 'a + Borrow<I>,
        Box<T>: From<&'b I>,
        I: Eq + std::hash::Hash + ?Sized,
    {
        let mut m = self.data.lock();
        if let Some(b) = m.get(val) {
            let p = b.as_ref() as *const T;
            return ArenaIntern {
                pointer: unsafe { &*p },
            };
        }
        let b: Box<T> = val.into();
        let p = b.as_ref() as *const T;
        m.insert(b);
        ArenaIntern {
            pointer: unsafe { &*p },
        }
    }
    fn intern_from_owned<I>(&self, val: I) -> ArenaIntern<T>
    where
        Box<T>: From<I>,
        I: Eq + std::hash::Hash + AsRef<T>,
    {
        let mut m = self.data.lock();
        if let Some(b) = m.get(val.as_ref()) {
            let p = b.as_ref() as *const T;
            return ArenaIntern {
                pointer: unsafe { &*p },
            };
        }
        let b: Box<T> = val.into();
        let p = b.as_ref() as *const T;
        m.insert(b);
        ArenaIntern {
            pointer: unsafe { &*p },
        }
    }
}
impl Arena<str> {
    /// Intern a `&str` as `ArenaIntern<str>`.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the `str` previously allocated.
    pub fn intern<'a, 'b>(&'a self, val: &'b str) -> ArenaIntern<'a, str> {
        self.intern_ref(val)
    }
    /// Intern a `String` as `ArenaIntern<str>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `String`.  Otherwise, it will free its input `String` and
    /// return a pointer to the `str` previously saved.
    pub fn intern_string(&self, val: String) -> ArenaIntern<str> {
        self.intern_from_owned(val)
    }
    /// Intern a `Box<str>` as `ArenaIntern<str>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `Box<str>`.  Otherwise, it will free its input `Box<str>`
    /// and return a pointer to the `str` previously saved.
    pub fn intern_box(&self, val: Box<str>) -> ArenaIntern<str> {
        self.intern_from_owned(val)
    }
}
impl Arena<std::ffi::CStr> {
    /// Intern a `&CStr` as `ArenaIntern<CStr>`.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the `CStr` previously allocated.
    pub fn intern<'a, 'b>(&'a self, val: &'b std::ffi::CStr) -> ArenaIntern<'a, std::ffi::CStr> {
        self.intern_ref(val)
    }
    /// Intern a `CString` as `ArenaIntern<CStr>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `CString`.  Otherwise, it will free its input `CString` and
    /// return a pointer to the `CStr` previously saved.
    pub fn intern_cstring(&self, val: std::ffi::CString) -> ArenaIntern<std::ffi::CStr> {
        self.intern_from_owned(val)
    }
    /// Intern a `Box<CStr>` as `ArenaIntern<CStr>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `Box<CSr>`.  Otherwise, it will free its input `Box<CStr>`
    /// and return a pointer to the `CStr` previously saved.
    pub fn intern_box(&self, val: Box<std::ffi::CStr>) -> ArenaIntern<std::ffi::CStr> {
        self.intern_from_owned(val)
    }
}
impl Arena<std::ffi::OsStr> {
    /// Intern a `&OsStr` as `ArenaIntern<OsStr>`.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the `OsStr` previously allocated.
    pub fn intern<'a, 'b>(&'a self, val: &'b std::ffi::OsStr) -> ArenaIntern<'a, std::ffi::OsStr> {
        self.intern_ref(val)
    }
    /// Intern a `OsString` as `ArenaIntern<OsStr>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `OsString`.  Otherwise, it will free its input `OsString` and
    /// return a pointer to the `OsStr` previously saved.
    pub fn intern_osstring(&self, val: std::ffi::OsString) -> ArenaIntern<std::ffi::OsStr> {
        self.intern_from_owned(val)
    }
    /// Intern a `Box<OsStr>` as `ArenaIntern<OsStr>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `Box<CSr>`.  Otherwise, it will free its input `Box<OsStr>`
    /// and return a pointer to the `OsStr` previously saved.
    pub fn intern_box(&self, val: Box<std::ffi::OsStr>) -> ArenaIntern<std::ffi::OsStr> {
        self.intern_from_owned(val)
    }
}
impl Arena<std::path::Path> {
    /// Intern a `&Path` as `ArenaIntern<Path>`.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the `Path` previously allocated.
    pub fn intern<'a, 'b>(&'a self, val: &'b std::path::Path) -> ArenaIntern<'a, std::path::Path> {
        self.intern_ref(val)
    }
    /// Intern a `PathBuf` as `ArenaIntern<Path>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `PathBuf`.  Otherwise, it will free its input `PathBuf` and
    /// return a pointer to the `Path` previously saved.
    pub fn intern_pathbuf(&self, val: std::path::PathBuf) -> ArenaIntern<std::path::Path> {
        self.intern_from_owned(val)
    }
    /// Intern a `Box<Path>` as `ArenaIntern<Path>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `Box<CSr>`.  Otherwise, it will free its input `Box<Path>`
    /// and return a pointer to the `Path` previously saved.
    pub fn intern_box(&self, val: Box<std::path::Path>) -> ArenaIntern<std::path::Path> {
        self.intern_from_owned(val)
    }
}
impl<T: Eq + Hash + Copy> Arena<[T]> {
    /// Intern a `&\[T\]` as `ArenaIntern<[T]>`.
    ///
    /// If this value has not previously been interned, then `intern` will
    /// allocate a spot for the value on the heap.  Otherwise, it will return a
    /// pointer to the `\[T\]` previously allocated.
    pub fn intern<'a, 'b>(&'a self, val: &'b [T]) -> ArenaIntern<'a, [T]> {
        self.intern_ref(val)
    }
    /// Intern a `Vec<T>` as `ArenaIntern<[T]>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `Vec<T>`.  Otherwise, it will free its input `Vec<T>` and
    /// return a pointer to the `[T]` previously saved.
    pub fn intern_vec(&self, val: Vec<T>) -> ArenaIntern<[T]> {
        self.intern_from_owned(val)
    }
    /// Intern a `Box<[T]>` as `ArenaIntern<[T]>`.
    ///
    /// If this value has not previously been interned, then `intern` will save
    /// the provided `Box<CSr>`.  Otherwise, it will free its input `Box<[T]>`
    /// and return a pointer to the `[T]` previously saved.
    pub fn intern_box(&self, val: Box<[T]>) -> ArenaIntern<[T]> {
        self.intern_from_owned(val)
    }
}
impl<T: Eq + Hash + ?Sized> Arena<T> {
    /// Intern a reference to a type that can be converted into a `Box<T>` as `ArenaIntern<T>`.
    pub fn intern_from<'a, 'b, I>(&'a self, val: &'b I) -> ArenaIntern<'a, T>
    where
        T: 'a + Borrow<I> + From<&'b I>,
        I: Eq + std::hash::Hash + ?Sized,
    {
        let mut m = self.data.lock();
        if let Some(b) = m.get(val) {
            let p = b.as_ref() as *const T;
            return ArenaIntern {
                pointer: unsafe { &*p },
            };
        }
        let b: Box<T> = Box::new(val.into());
        let p = b.as_ref() as *const T;
        m.insert(b);
        ArenaIntern {
            pointer: unsafe { &*p },
        }
    }
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T: ?Sized> AsRef<T> for ArenaIntern<'a, T> {
    fn as_ref(&self) -> &T {
        self.pointer
    }
}

impl<'a, T: ?Sized> std::ops::Deref for ArenaIntern<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'a, T: ?Sized> ArenaIntern<'a, T> {
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
    pub fn into_ref(self) -> &'a T {
        self.pointer
    }
}

/// The hash implementation returns the hash of the pointer
/// value, not the hash of the value pointed to.  This should
/// be irrelevant, since there is a unique pointer for every
/// value, but it *is* observable, since you could compare the
/// hash of the pointer with hash of the data itself.
impl<'a, T: ?Sized> Hash for ArenaIntern<'a, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_pointer().hash(state);
    }
}

impl<'a, T: ?Sized> PartialEq for ArenaIntern<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self.get_pointer() == other.get_pointer()
    }
}
impl<'a, T: ?Sized> Eq for ArenaIntern<'a, T> {}

// #[cfg(feature = "arena")]
// create_impls_no_new!(ArenaIntern, arenaintern_impl_tests, ['a], [Eq, Hash], [Eq, Hash]);

impl<'a, T: std::fmt::Debug + ?Sized> std::fmt::Debug for ArenaIntern<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        std::fmt::Debug::fmt(&self.get_pointer(), f)?;
        f.write_str(" : ")?;
        self.as_ref().fmt(f)
    }
}

impl<'a, T: std::fmt::Display + ?Sized> std::fmt::Display for ArenaIntern<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
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
    use std::ops::Deref;
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
