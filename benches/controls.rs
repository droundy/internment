//! Controls for `versions.rs`: the same comparisons, but between two copies of
//! the *same* code, to measure what compiling it twice does by itself.
//!
//! Every group has two candidates running the same operation against the same
//! release, once in each of two separately compiled copies of the timing code
//! (`old/old` against the previous release, `cur/cur` against this one).  Any
//! gap is the placement of code, not a difference in internment.  A difference
//! in `versions.rs` smaller than the gaps here is not evidence of anything.
//!
//! These do not control for the library itself being compiled twice, which
//! would need a copy of the previous release's source built as a second
//! package; they only separate the benchmark code from the library.

#[macro_use]
mod common;

#[global_allocator]
static ALLOC: scaling::Allocator = scaling::Allocator::new();

/// Two candidates doing the same thing, the second reported against the first.
macro_rules! twins {
    ($group:literal, $a:ident, $b:ident, $krate:ident, |$k:ident, $arg:ident: $ty:ty| -> $ret:ty $body:block) => {
        #[scaling::bench(group = $group, name = "first", baseline)]
        #[allow(unused_braces)]
        fn $a($arg: $ty) -> $ret {
            use ::$krate as $k;
            $body
        }
        #[scaling::bench(group = $group, name = "second")]
        #[allow(unused_braces)]
        fn $b($arg: $ty) -> $ret {
            use ::$krate as $k;
            $body
        }
    };
}

strings_input!(
    "old/old Intern<String>::new long",
    "old/old Intern<String>::new short",
    "old/old Intern<String> lookup",
    "old/old Intern<String> sort",
    "old/old Intern<String> any eq",
    "old/old ArcIntern<String>::new long",
    "old/old ArcIntern<String>::new short",
    "old/old ArcIntern<String> lookup",
    "old/old ArcIntern<String> sort",
    "old/old ArcIntern<String> any eq",
    "cur/cur Intern<String>::new long",
    "cur/cur Intern<String>::new short",
    "cur/cur Intern<String> lookup",
    "cur/cur Intern<String> sort",
    "cur/cur Intern<String> any eq",
    "cur/cur ArcIntern<String>::new long",
    "cur/cur ArcIntern<String>::new short",
    "cur/cur ArcIntern<String> lookup",
    "cur/cur ArcIntern<String> sort",
    "cur/cur ArcIntern<String> any eq",
);
random_i64_input!(
    "old/old Intern<i64>::new random",
    "old/old ArcIntern<i64>::new random",
    "cur/cur Intern<i64>::new random",
    "cur/cur ArcIntern<i64>::new random",
);

twins!(
    "old/old Intern<String>::new long",
    old_intern_new_long_a,
    old_intern_new_long_b,
    internment_old,
    |K, s: &common::Strings| -> usize { common::build_set(&s.long, K::Intern::new) }
);
twins!(
    "old/old Intern<String>::new short",
    old_intern_new_short_a,
    old_intern_new_short_b,
    internment_old,
    |K, s: &common::Strings| -> usize { common::build_set(&s.short, K::Intern::new) }
);
twins!(
    "old/old Intern<String> lookup",
    old_intern_lookup_a,
    old_intern_lookup_b,
    internment_old,
    |K, s: &common::Strings| -> impl FnMut() -> usize {
        common::lookup(&s.long, &s.long_other, K::Intern::new)
    }
);
twins!(
    "old/old Intern<String> sort",
    old_intern_sort_a,
    old_intern_sort_b,
    internment_old,
    |K, s: &common::Strings| -> impl FnMut() -> usize { common::sort(&s.long, K::Intern::new) }
);
twins!(
    "old/old Intern<String> any eq",
    old_intern_any_eq_a,
    old_intern_any_eq_b,
    internment_old,
    |K, s: &common::Strings| -> impl FnMut() -> usize { common::any_eq(&s.long, K::Intern::new) }
);
twins!(
    "old/old Intern<i64>::new random",
    old_intern_new_i64_a,
    old_intern_new_i64_b,
    internment_old,
    |K, x: &mut i64| -> () {
        K::Intern::new(*x);
    }
);
twins!(
    "old/old ArcIntern<String>::new long",
    old_arc_new_long_a,
    old_arc_new_long_b,
    internment_old,
    |K, s: &common::Strings| -> usize { common::build_set(&s.long, K::ArcIntern::new) }
);
twins!(
    "old/old ArcIntern<String>::new short",
    old_arc_new_short_a,
    old_arc_new_short_b,
    internment_old,
    |K, s: &common::Strings| -> usize { common::build_set(&s.short, K::ArcIntern::new) }
);
twins!(
    "old/old ArcIntern<String> lookup",
    old_arc_lookup_a,
    old_arc_lookup_b,
    internment_old,
    |K, s: &common::Strings| -> impl FnMut() -> usize {
        common::lookup(&s.long, &s.long_other, K::ArcIntern::new)
    }
);
twins!(
    "old/old ArcIntern<String> sort",
    old_arc_sort_a,
    old_arc_sort_b,
    internment_old,
    |K, s: &common::Strings| -> impl FnMut() -> usize { common::sort(&s.long, K::ArcIntern::new) }
);
twins!(
    "old/old ArcIntern<String> any eq",
    old_arc_any_eq_a,
    old_arc_any_eq_b,
    internment_old,
    |K, s: &common::Strings| -> impl FnMut() -> usize {
        common::any_eq(&s.long, K::ArcIntern::new)
    }
);
twins!(
    "old/old ArcIntern<i64>::new random",
    old_arc_new_i64_a,
    old_arc_new_i64_b,
    internment_old,
    |K, x: &mut i64| -> () {
        K::ArcIntern::new(*x);
    }
);
twins!(
    "cur/cur Intern<String>::new long",
    cur_intern_new_long_a,
    cur_intern_new_long_b,
    internment,
    |K, s: &common::Strings| -> usize { common::build_set(&s.long, K::Intern::new) }
);
twins!(
    "cur/cur Intern<String>::new short",
    cur_intern_new_short_a,
    cur_intern_new_short_b,
    internment,
    |K, s: &common::Strings| -> usize { common::build_set(&s.short, K::Intern::new) }
);
twins!(
    "cur/cur Intern<String> lookup",
    cur_intern_lookup_a,
    cur_intern_lookup_b,
    internment,
    |K, s: &common::Strings| -> impl FnMut() -> usize {
        common::lookup(&s.long, &s.long_other, K::Intern::new)
    }
);
twins!(
    "cur/cur Intern<String> sort",
    cur_intern_sort_a,
    cur_intern_sort_b,
    internment,
    |K, s: &common::Strings| -> impl FnMut() -> usize { common::sort(&s.long, K::Intern::new) }
);
twins!(
    "cur/cur Intern<String> any eq",
    cur_intern_any_eq_a,
    cur_intern_any_eq_b,
    internment,
    |K, s: &common::Strings| -> impl FnMut() -> usize { common::any_eq(&s.long, K::Intern::new) }
);
twins!(
    "cur/cur Intern<i64>::new random",
    cur_intern_new_i64_a,
    cur_intern_new_i64_b,
    internment,
    |K, x: &mut i64| -> () {
        K::Intern::new(*x);
    }
);
twins!(
    "cur/cur ArcIntern<String>::new long",
    cur_arc_new_long_a,
    cur_arc_new_long_b,
    internment,
    |K, s: &common::Strings| -> usize { common::build_set(&s.long, K::ArcIntern::new) }
);
twins!(
    "cur/cur ArcIntern<String>::new short",
    cur_arc_new_short_a,
    cur_arc_new_short_b,
    internment,
    |K, s: &common::Strings| -> usize { common::build_set(&s.short, K::ArcIntern::new) }
);
twins!(
    "cur/cur ArcIntern<String> lookup",
    cur_arc_lookup_a,
    cur_arc_lookup_b,
    internment,
    |K, s: &common::Strings| -> impl FnMut() -> usize {
        common::lookup(&s.long, &s.long_other, K::ArcIntern::new)
    }
);
twins!(
    "cur/cur ArcIntern<String> sort",
    cur_arc_sort_a,
    cur_arc_sort_b,
    internment,
    |K, s: &common::Strings| -> impl FnMut() -> usize { common::sort(&s.long, K::ArcIntern::new) }
);
twins!(
    "cur/cur ArcIntern<String> any eq",
    cur_arc_any_eq_a,
    cur_arc_any_eq_b,
    internment,
    |K, s: &common::Strings| -> impl FnMut() -> usize {
        common::any_eq(&s.long, K::ArcIntern::new)
    }
);
twins!(
    "cur/cur ArcIntern<i64>::new random",
    cur_arc_new_i64_a,
    cur_arc_new_i64_b,
    internment,
    |K, x: &mut i64| -> () {
        K::ArcIntern::new(*x);
    }
);

fn main() -> Result<(), scaling::RegistrationError> {
    common::config(0.01, 10.0).run_and_print()
}
