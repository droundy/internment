//! Rough comparisons between this crate's interners and what they replace or
//! compete with: plain `String`s in a `HashSet`, and the `arc-interner` crate.
//!
//! They differ by factors, not by percentages, so each is measured only to 10%.
//! The comparisons that need accuracy, this release against the previous one,
//! are in `versions.rs`.
//!
//! Each group is one operation and every candidate runs the same code on the
//! same strings, with `String` the baseline of the groups that have it:
//!
//! - `new long` and `new short` build a set of 2999 values from long and short
//!   strings; an interner that is a table of what was seen already finds
//!   everything the second time, so these measure a lookup and a copy;
//! - `lookup` looks up 999 values that are not in a set of 2999;
//! - `sort` sorts 2999 values;
//! - `any eq` scans 2999 for one that is not there;
//! - the `i64` groups intern a random number, and clone one.
//!
//! The same code in each candidate lives in `common`, generic over how a
//! `String` becomes a value.

#[macro_use]
mod common;

use internment::{ArcIntern, Intern, Intern32, NewIntern};

#[global_allocator]
static ALLOC: scaling::Allocator = scaling::Allocator::new();

strings_input!("new long", "new short", "lookup", "sort", "any eq");
random_i64_input!("new i64", "clone i64");

/// The candidates of every `&Strings` group for one way of making a value from
/// a `String`; in a module of its own so that every one can have the same names.
macro_rules! string_candidates {
    ($m:ident, $label:literal, $ctor:expr $(, baseline $base:ident)?) => {
        mod $m {
            use super::*;

            #[scaling::bench(group = "new long", name = $label $(, $base)?)]
            fn new_long(s: &common::Strings) -> usize {
                common::build_set(&s.long, $ctor)
            }
            #[scaling::bench(group = "new short", name = $label $(, $base)?)]
            fn new_short(s: &common::Strings) -> usize {
                common::build_set(&s.short, $ctor)
            }
            #[scaling::bench(group = "lookup", name = $label $(, $base)?)]
            fn lookup(s: &common::Strings) -> impl FnMut() -> usize {
                common::lookup(&s.long, &s.long_other, $ctor)
            }
            #[scaling::bench(group = "sort", name = $label $(, $base)?)]
            fn sort(s: &common::Strings) -> impl FnMut() -> usize {
                common::sort(&s.long, $ctor)
            }
            #[scaling::bench(group = "any eq", name = $label $(, $base)?)]
            fn any_eq(s: &common::Strings) -> impl FnMut() -> usize {
                common::any_eq(&s.long, $ctor)
            }
        }
    };
}

string_candidates!(plain, "String", |s: String| s, baseline baseline);
string_candidates!(intern, "Intern", |s: String| Intern::new(s));
string_candidates!(new_intern, "NewIntern", |s: String| NewIntern::new(s));
string_candidates!(arc, "ArcIntern", |s: String| ArcIntern::new(s));
string_candidates!(intern32, "Intern32", |s: String| Intern32::new(s));
string_candidates!(arc_interner, "arc_interner", |s: String| {
    ::arc_interner::ArcIntern::new(s)
});

/// The candidates of the `i64` groups: interning a random number, which is new
/// the first time, and cloning an interned value.
macro_rules! int_candidates {
    ($m:ident, $label:literal, $new:expr $(, baseline $base:ident)?) => {
        mod $m {
            use super::*;

            #[scaling::bench(group = "new i64", name = $label $(, $base)?)]
            fn new_i64(x: &mut i64) {
                let new = $new;
                new(*x);
            }
            #[scaling::bench(group = "clone i64", name = $label $(, $base)?)]
            fn clone_i64(x: &i64) -> impl FnMut() -> i64 {
                let i = ($new)(*x);
                move || *i.clone()
            }
        }
    };
}

int_candidates!(intern_i64, "Intern", |x: i64| Intern::new(x), baseline baseline);
int_candidates!(new_intern_i64, "NewIntern", |x: i64| NewIntern::new(x));
int_candidates!(arc_i64, "ArcIntern", |x: i64| ArcIntern::new(x));
int_candidates!(intern32_i64, "Intern32", |x: i64| Intern32::new(x));
int_candidates!(arc_interner_i64, "arc_interner", |x: i64| {
    ::arc_interner::ArcIntern::new(x)
});

fn main() -> Result<(), scaling::RegistrationError> {
    common::config(0.1, 10.0).run_and_print()
}
