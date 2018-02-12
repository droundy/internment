Internment
==========

A very easy to use libray for
[interning](https://en.wikipedia.org/wiki/String_interning) strings or
other data in rust.  This library has no support for freeing data
once they are interned.  But on the plus side, if you intern the same
data many times, only one copy need be allocated.

Usage:

```rust
let x = Intern::new("hello");
```
