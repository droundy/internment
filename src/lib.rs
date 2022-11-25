#![deny(missing_docs)]
// Copyright 2018,2020 David Roundy
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! A very easy to use library for
//! [interning](https://en.wikipedia.org/wiki/String_interning)
//! strings or other data in rust.  Interned data is very efficient to
//! either hash or compare for equality (just a pointer comparison).
//! Data is also automatically de-duplicated.
//!
//! You have three options with the internment crate:
//!
//! 1. `Intern`, which will never free your data.  This means that an
//! `Intern` is `Copy`, so you can make as many copies of the pointer
//! as you may care to at no cost.
//!
//! 2. `ArcIntern`, which reference-counts your data and frees it when
//! there are no more references.  `ArcIntern` will keep memory use
//! down, but uses an atomic increment/decrement whenever a clone of
//! your pointer is made, or a pointer is dropped.
//!
//! 3. `ArenaIntern`, which stores its data in an `Arena`, with the data being freed
//!   when the arena itself is freed.  Requires feature `arena`.
//!
//! In each case, accessing your data is a single pointer dereference, and the size
//! of any internment data structure (`Intern` or `ArcIntern` or `ArenaIntern`) is a
//! single pointer.  In each case, you have a guarantee that a single data value (as
//! defined by `Eq` and `Hash`) will correspond to a single pointer value.  This
//! means that we can use pointer comparison (and a pointer hash) in place of value
//! comparisons, which is very fast.
//!
//! # Example
//! ```rust
//! use internment::Intern;
//! let x = Intern::new("hello");
//! let y = Intern::new("world");
//! assert_ne!(x, y);
//! println!("The conventional greeting is '{} {}'", x, y);
//! ```

// Enable the `doc_cfg` feature when the `docsrs` configuration attribute is
// defined
#![cfg_attr(docsrs, feature(doc_cfg))]

mod boxedset;

#[cfg(feature = "append-only-vec")]
mod typearena;

#[doc(hidden)]
#[cfg(feature = "append-only-vec")]
pub use typearena::Intern as NewIntern;

#[cfg(feature = "intern")]
mod container;

#[cfg(feature = "intern")]
mod intern;
#[cfg(feature = "intern")]
pub use intern::Intern;

#[cfg(feature = "arena")]
mod arena;

#[cfg(feature = "arena")]
pub use arena::Arena;

#[cfg(feature = "arena")]
pub use arena::ArenaIntern;

#[cfg(feature = "arc")]
mod arc;
#[cfg(feature = "arc")]
mod arc_dst;

#[cfg(feature = "arc")]
pub use arc::ArcIntern;
