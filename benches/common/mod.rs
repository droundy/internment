//! Pieces shared by the benchmark binaries.
//!
//! Every comparison in these benchmarks is a `scaling` group whose candidates
//! take the same input type, so the work that depends on an interner type is
//! done by a candidate and the helpers here are generic over a constructor.
//! Every use of the previously published release is spelled `internment_old`,
//! and is confined to the `vs!` macro below and to `controls.rs`, so that
//! moving the comparison to a newer release is a change to one line of
//! `Cargo.toml` (see `plans/scaling-0.9.md`).
#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::HashSet;
use std::hash::Hash;
use std::rc::Rc;

/// The strings every set-building benchmark starts from.
///
/// `scaling` makes a new input for every iteration and clones it for every
/// candidate, so this holds shared vectors: cloning it is cheap and the
/// candidates only read it.
#[derive(Clone)]
pub struct Strings {
    /// 2999 distinct strings of about 530 bytes, in a fixed shuffled order.
    pub long: Rc<Vec<String>>,
    /// 999 distinct long strings, none of them in `long`.
    pub long_other: Rc<Vec<String>>,
    /// 2999 distinct strings of at most four bytes.
    pub short: Rc<Vec<String>>,
}

fn shuffled(mut v: Vec<String>) -> Vec<String> {
    // A fixed pseudo-random order (the original benchmarks iterated a
    // `HashSet`, which is random), so that sorting has something to do.
    let mut state = 0x2545_f491_4f6c_dd1du64;
    for i in (1..v.len()).rev() {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        v.swap(i, (state % (i as u64 + 1)) as usize);
    }
    v
}

thread_local! {
    static STRINGS: Strings = Strings {
        long: Rc::new(shuffled(
            (1..3000)
                .map(|i| format!("hello this is a pretty long string {:500}", i))
                .collect(),
        )),
        long_other: Rc::new(shuffled(
            (1..1000)
                .map(|i| format!("hello this is a pretty long string also {:500}", i))
                .collect(),
        )),
        short: Rc::new(shuffled((1..3000).map(|i| format!("{}", i)).collect())),
    };
    static RNG: RefCell<u64> = const { RefCell::new(0x9e37_79b9_7f4a_7c15) };
}

pub fn strings() -> Strings {
    STRINGS.with(|s| s.clone())
}

/// A random 64 bit number: cheap, and different on each call.
pub fn random_u64() -> u64 {
    RNG.with(|r| {
        let mut x = r.borrow_mut();
        *x ^= *x << 13;
        *x ^= *x >> 7;
        *x ^= *x << 17;
        *x
    })
}

/// Declares the input of the benchmark groups named, which all take `&Strings`.
macro_rules! strings_input {
    ($($group:literal),* $(,)?) => {
        #[scaling::input(group($($group),*), name = "")]
        fn strings_input() -> common::Strings {
            common::strings()
        }
    };
}

/// Declares an input that is a fresh random `i64` each time.
macro_rules! random_i64_input {
    ($($group:literal),* $(,)?) => {
        #[scaling::input(group($($group),*), name = "")]
        fn random_i64_input() -> i64 {
            common::random_u64() as i64
        }
    };
}

/// Declares an input that is a fresh random `u8` each time.
macro_rules! random_u8_input {
    ($($group:literal),* $(,)?) => {
        #[scaling::input(group($($group),*), name = "")]
        fn random_u8_input() -> u8 {
            common::random_u64() as u8
        }
    };
}

/// Two candidates of a group, the baseline running the body against the
/// previously published release (`internment_old`) and the other against this
/// one, with the crate named by `$k` inside the body.  The types are token
/// trees, not `ty` fragments, because `scaling`'s attributes do not see
/// through the invisible group around a `ty` and take `&I` for an input by value.
macro_rules! vs {
    ($group:literal, $old:ident, $new:ident, $k:ident, $arg:ident: [$($ty:tt)+] -> [$($ret:tt)+] $body:expr) => {
        #[scaling::bench(group = $group, name = "old", baseline)]
        fn $old($arg: $($ty)+) -> $($ret)+ {
            use ::internment_old as $k;
            $body
        }
        #[scaling::bench(group = $group, name = "new")]
        fn $new($arg: $($ty)+) -> $($ret)+ {
            use ::internment as $k;
            $body
        }
    };
}

/// Builds a set of `ctor(s)` for each of `strings`, which the candidate does
/// on every call.
pub fn build_set<T: Eq + Hash>(strings: &[String], ctor: impl Fn(String) -> T) -> usize {
    let mut n = HashSet::new();
    for x in strings {
        n.insert(ctor(x.clone()));
    }
    n.len()
}

/// Like `build_set`, but constructing from a reference instead.
pub fn build_set_from_ref<T: Eq + Hash>(strings: &[String], ctor: impl Fn(&str) -> T) -> usize {
    let mut n = HashSet::new();
    for x in strings {
        n.insert(ctor(x));
    }
    n.len()
}

/// Looks up each of `b` in a set made of `a`: they have nothing in common, so
/// this hashes and compares without finding anything.  The setup, which is
/// not timed, builds both.
pub fn lookup<T: Eq + Hash>(
    a: &[String],
    b: &[String],
    ctor: impl Fn(String) -> T,
) -> impl FnMut() -> usize {
    let a: HashSet<T> = a.iter().cloned().map(&ctor).collect();
    let b: Vec<T> = b.iter().cloned().map(&ctor).collect();
    move || b.iter().filter(|x| a.contains(x)).count()
}

/// Sorts references to values made from `strings`, so that what is timed is
/// the comparisons and not copying the values (a `String` is expensive to
/// copy, an interned value is not).
pub fn sort<T: Ord>(strings: &[String], ctor: impl Fn(String) -> T) -> impl FnMut() -> usize {
    let v: Vec<T> = strings.iter().cloned().map(ctor).collect();
    move || {
        let mut w: Vec<&T> = v.iter().collect();
        w.sort();
        w.len()
    }
}

/// Scans values made from `strings` for one equal to a string that is not in
/// them.
pub fn any_eq<T: PartialEq>(
    strings: &[String],
    ctor: impl Fn(String) -> T,
) -> impl FnMut() -> usize {
    let v: Vec<T> = strings.iter().cloned().map(&ctor).collect();
    let value = ctor("hello this is a pretty long string".to_string());
    move || v.iter().any(|s| *s == value) as usize
}

/// The `Config` every benchmark binary starts from, given how precisely it
/// should measure and how long each group may take to do so.
///
/// `cargo bench --features benchmarks --bench versions -- sort` runs only the
/// groups with `sort` in their name, and `INTERNMENT_BENCH_MAX_SECS` replaces
/// the time each group may take (to see that something runs, not to measure it).
pub fn config(relative_error: f64, max_secs: f64) -> scaling::Config {
    let max_secs = std::env::var("INTERNMENT_BENCH_MAX_SECS")
        .ok()
        .and_then(|s| s.parse::<f64>().ok())
        .unwrap_or(max_secs);
    let mut config = scaling::Config::default()
        .with_relative_error(relative_error)
        .with_max_time(std::time::Duration::from_secs_f64(max_secs));
    if let Some(wanted) = std::env::args().skip(1).find(|a| !a.starts_with('-')) {
        config = config.filter_groups(move |group| group.contains(&wanted));
    }
    config
}
