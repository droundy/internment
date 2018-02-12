Internment
==========

A very easy to use library for
[interning](https://en.wikipedia.org/wiki/String_interning)
strings or other data in rust.  Interned data is very efficient to
either hash or compare for equality (just a pointer comparison).
Data is also automatically de-duplicated.

You have two options with the internment crate:

1. `Intern`, which will never free your data.  This means that an
`Intern` is `Copy`, so you can make as many copies of the pointer
as you may care to at no cost.

2. `ArcIntern`, which reference-counts your data and frees it when
there are no more references.  `ArcIntern` will keep memory use
down, but requires locking whenever a clone of your pointer is
made, as well as when dropping the pointer.

In both cases, accessing your data is a single pointer
dereference, and the size of either `Intern` or `ArcIntern` is a
single pointer.  In both cases, you have a guarantee that a single
data value (as defined by `Eq` and `Hash`) will correspond to a
single pointer value.  This means that we can use pointer
comparison (and a pointer hash) in place of value comparisons,
which is very fast.

# Example
```rust
use internment::Intern;
let x = Intern::new("hello");
let y = Intern::new("world");
assert_ne!(x, y);
```
