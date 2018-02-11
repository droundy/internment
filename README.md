Internment
==========

A very easy to use libray for
[interning](https://en.wikipedia.org/wiki/String_interning) strings or
other data in rust.  This library has no support for freeing strings
once they are interned.  But on the plus side, the data use is very low.

Usage:

```rust
let x = Intern::new("hello");
```
