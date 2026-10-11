//! This release of internment against the previous one (`internment_old`), at
//! the default accuracy of 1%, for checking whether a change made anything
//! faster or slower.
//!
//! Every group has two candidates, `old` (the baseline) and `new`, running the
//! same code against the two releases, so each comparison is the pair that
//! matters, measured directly on the same inputs.  Groups are named after the
//! operation: `Intern<String>::new long` builds a set of 2999 `Intern<String>`
//! from long strings, and so on.  Setup that is not part of the operation, such
//! as building the sets that a lookup searches, is not timed.
//!
//! Before believing a small difference, run `controls`, which compares a
//! release with itself.  See the "Benchmarking" section of the README for how
//! to run this.

#[macro_use]
mod common;

#[global_allocator]
static ALLOC: scaling::Allocator = scaling::Allocator::new();

strings_input!(
    "Intern<String>::new long",
    "Intern<String>::new short",
    "Intern<String>::from long",
    "Intern<String> lookup",
    "Intern<String> sort",
    "Intern<String> any eq",
    "ArcIntern<String>::new long",
    "ArcIntern<String>::new short",
    "ArcIntern<String>::from long",
    "ArcIntern<String> lookup",
    "ArcIntern<String> sort",
    "ArcIntern<String> any eq",
);
random_i64_input!(
    "Intern<i64>::new random",
    "Intern<i64>::clone",
    "ArcIntern<i64>::new random",
    "ArcIntern<i64>::clone",
);
random_u8_input!("Intern<u8>::new", "ArcIntern<u8>::new",);

vs!("Intern<String>::new long", intern_new_long_old, intern_new_long_new, K, s: [&common::Strings] -> [usize] common::build_set(&s.long, K::Intern::new));
vs!("Intern<String>::new short", intern_new_short_old, intern_new_short_new, K, s: [&common::Strings] -> [usize] common::build_set(&s.short, K::Intern::new));
vs!("Intern<String>::from long", intern_from_long_old, intern_from_long_new, K, s: [&common::Strings] -> [usize] common::build_set_from_ref(&s.long, |x| K::Intern::<String>::from_ref(x)));
vs!("Intern<String> lookup", intern_lookup_old, intern_lookup_new, K, s: [&common::Strings] -> [impl FnMut() -> usize] common::lookup(&s.long, &s.long_other, K::Intern::new));
vs!("Intern<String> sort", intern_sort_old, intern_sort_new, K, s: [&common::Strings] -> [impl FnMut() -> usize] common::sort(&s.long, K::Intern::new));
vs!("Intern<String> any eq", intern_any_eq_old, intern_any_eq_new, K, s: [&common::Strings] -> [impl FnMut() -> usize] common::any_eq(&s.long, K::Intern::new));
vs!("Intern<i64>::new random", intern_new_i64_old, intern_new_i64_new, K, x: [&mut i64] -> [()] { K::Intern::new(*x); });
vs!("Intern<i64>::clone", intern_clone_old, intern_clone_new, K, x: [&i64] -> [impl FnMut() -> i64] { let i = K::Intern::new(*x); move || *i.clone() });
vs!("Intern<u8>::new", intern_new_u8_old, intern_new_u8_new, K, x: [&mut u8] -> [()] { K::Intern::new(*x); });
vs!("ArcIntern<String>::new long", arc_new_long_old, arc_new_long_new, K, s: [&common::Strings] -> [usize] common::build_set(&s.long, K::ArcIntern::new));
vs!("ArcIntern<String>::new short", arc_new_short_old, arc_new_short_new, K, s: [&common::Strings] -> [usize] common::build_set(&s.short, K::ArcIntern::new));
vs!("ArcIntern<String>::from long", arc_from_long_old, arc_from_long_new, K, s: [&common::Strings] -> [usize] common::build_set_from_ref(&s.long, |x| K::ArcIntern::<String>::from_ref(x)));
vs!("ArcIntern<String> lookup", arc_lookup_old, arc_lookup_new, K, s: [&common::Strings] -> [impl FnMut() -> usize] common::lookup(&s.long, &s.long_other, K::ArcIntern::new));
vs!("ArcIntern<String> sort", arc_sort_old, arc_sort_new, K, s: [&common::Strings] -> [impl FnMut() -> usize] common::sort(&s.long, K::ArcIntern::new));
vs!("ArcIntern<String> any eq", arc_any_eq_old, arc_any_eq_new, K, s: [&common::Strings] -> [impl FnMut() -> usize] common::any_eq(&s.long, K::ArcIntern::new));
vs!("ArcIntern<i64>::new random", arc_new_i64_old, arc_new_i64_new, K, x: [&mut i64] -> [()] { K::ArcIntern::new(*x); });
vs!("ArcIntern<i64>::clone", arc_clone_old, arc_clone_new, K, x: [&i64] -> [impl FnMut() -> i64] { let i = K::ArcIntern::new(*x); move || *i.clone() });
vs!("ArcIntern<u8>::new", arc_new_u8_old, arc_new_u8_new, K, x: [&mut u8] -> [()] { K::ArcIntern::new(*x); });

fn main() -> Result<(), scaling::RegistrationError> {
    common::config(0.01, 10.0).run_and_print()
}
