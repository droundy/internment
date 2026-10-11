//! Workloads that intern many values, run from one thread and from fifty
//! threads at once, to see how each interner behaves when its table is
//! contended.
//!
//! Each workload is two groups, `<workload> contended` and `<workload>
//! uncontended`, with one candidate per interner.  A call of a candidate does
//! the same work of interning 100000 values fifty times: the uncontended one
//! in a row on the calling thread, the contended one on fifty threads at once.
//! They clear the interner's table first, so what is measured is a table that
//! starts empty (which `Arena`, a table of its own that is dropped at the end of
//! each pass, never needs).
//!
//! **Run this on a machine whose benchmark CPUs are not pinned to one core.**
//! `scaling` pins a benchmark to the CPUs of a `quiet-bench` reservation if
//! there is one, and threads inherit that, so with one reserved CPU the fifty
//! threads take turns on it and "contended" means something else.  Either
//! reserve several CPUs (`quiet-bench reserve 2-5`) or set `SCALING_NO_PIN=1`.
//!
//! Every call takes of the order of a second, so a full run is long: select
//! with an argument (`cargo bench --features benchmarks --bench contended --
//! "few strings"`) or lower `INTERNMENT_BENCH_MAX_SECS`.

#[macro_use]
mod common;

use internment::{ArcIntern, Arena, Intern, Intern32, NewIntern};

// The workloads: a macro each, of an interner type and a number to vary the
// values by, which is run once per thread.

macro_rules! four_types {
    ($intern:ident, $i:expr) => {
        $intern::<String>::benchmarking_only_clear_interns();
        $intern::<usize>::benchmarking_only_clear_interns();
        $intern::<(usize, usize)>::benchmarking_only_clear_interns();
        $intern::<(usize, usize, usize)>::benchmarking_only_clear_interns();

        let mut interned_strings = Vec::new();
        let mut interned_ints = Vec::new();
        let mut interned_pairs = Vec::new();
        let mut interned_triples = Vec::new();
        for n in 0..100000 {
            match ($i + n) % 4 {
                0 => {
                    interned_strings.push($intern::new(format!("i {} and n {}", $i, n)));
                }
                1 => {
                    interned_ints.push($intern::new($i * n * 137));
                }
                2 => {
                    interned_pairs.push($intern::new(($i, n)));
                }
                _ => {
                    interned_triples.push($intern::new(($i, n, $i + n)));
                }
            }
        }
    };
}

macro_rules! same_arrays {
    ($intern:ident, $i:expr) => {
        $intern::<[usize; 1000]>::benchmarking_only_clear_interns();
        $intern::<[usize; 20]>::benchmarking_only_clear_interns();
        $intern::<[usize; 30]>::benchmarking_only_clear_interns();
        $intern::<[usize; 40]>::benchmarking_only_clear_interns();
        $intern::<[usize; 50]>::benchmarking_only_clear_interns();
        $intern::<[usize; 60]>::benchmarking_only_clear_interns();
        $intern::<[usize; 70]>::benchmarking_only_clear_interns();
        $intern::<[usize; 80]>::benchmarking_only_clear_interns();
        $intern::<[usize; 90]>::benchmarking_only_clear_interns();
        $intern::<[usize; 100]>::benchmarking_only_clear_interns();

        let mut size = $i;
        for _ in 0..100000 {
            size = (size * 75 + 74) % ((1 << 16) + 1);
            match size % 10 {
                0 => {
                    $intern::new([0; 1000]);
                }
                1 => {
                    $intern::new([0; 20]);
                }
                2 => {
                    $intern::new([0; 30]);
                }
                3 => {
                    $intern::new([0; 40]);
                }
                4 => {
                    $intern::new([0; 50]);
                }
                5 => {
                    $intern::new([0; 60]);
                }
                6 => {
                    $intern::new([0; 70]);
                }
                7 => {
                    $intern::new([0; 80]);
                }
                8 => {
                    $intern::new([0; 90]);
                }
                _ => {
                    $intern::new([0; 100]);
                }
            }
        }
    };
}

macro_rules! different_arrays {
    ($intern:ident, $i:expr) => {
        $intern::<[usize; 1000]>::benchmarking_only_clear_interns();
        $intern::<[usize; 20]>::benchmarking_only_clear_interns();
        $intern::<[usize; 30]>::benchmarking_only_clear_interns();
        $intern::<[usize; 40]>::benchmarking_only_clear_interns();
        $intern::<[usize; 50]>::benchmarking_only_clear_interns();
        $intern::<[usize; 60]>::benchmarking_only_clear_interns();
        $intern::<[usize; 70]>::benchmarking_only_clear_interns();
        $intern::<[usize; 80]>::benchmarking_only_clear_interns();
        $intern::<[usize; 90]>::benchmarking_only_clear_interns();
        $intern::<[usize; 100]>::benchmarking_only_clear_interns();

        let mut size = $i;
        for _ in 0..100000 {
            size = (size * 75 + 74) % ((1 << 16) + 1);
            match size % 10 {
                0 => {
                    $intern::new([size + $i; 1000]);
                }
                1 => {
                    $intern::new([size + $i; 20]);
                }
                2 => {
                    $intern::new([size + $i; 30]);
                }
                3 => {
                    $intern::new([size + $i; 40]);
                }
                4 => {
                    $intern::new([size + $i; 50]);
                }
                5 => {
                    $intern::new([size + $i; 60]);
                }
                6 => {
                    $intern::new([size + $i; 70]);
                }
                7 => {
                    $intern::new([size + $i; 80]);
                }
                8 => {
                    $intern::new([size + $i; 90]);
                }
                _ => {
                    $intern::new([size + $i; 100]);
                }
            }
        }
    };
}

macro_rules! strings {
    ($intern:ident, $i:expr) => {
        $intern::<String>::benchmarking_only_clear_interns();

        let mut interned_strings = Vec::new();
        for n in 0..100000 {
            interned_strings.push($intern::new(format!("i {} and n {}", $i, n)));
        }
    };
}

macro_rules! arena_strings {
    ($intern:ident, $i:expr) => {
        let arena: Arena<String> = Arena::new();

        let mut interned_strings = Vec::new();
        for n in 0..100000 {
            interned_strings.push(arena.intern(format!("i {} and n {}", $i, n)));
        }
    };
}

macro_rules! few_strings {
    ($intern:ident, $i:expr) => {
        $intern::<String>::benchmarking_only_clear_interns();

        let mut interned_strings = Vec::new();
        for n in 0..100000 {
            interned_strings.push($intern::new(
                memorable_wordlist::WORDS[($i + n) % 10].to_string(),
            ));
        }
    };
}

macro_rules! few_str_from {
    ($intern:ident, $i:expr) => {
        $intern::<str>::benchmarking_only_clear_interns();

        let mut interned_strings: Vec<$intern<str>> = Vec::new();
        for n in 0..100000 {
            let i: $intern<str> = From::from(memorable_wordlist::WORDS[($i + n) % 10]);
            interned_strings.push(i);
        }
    };
}

macro_rules! few_strings_from {
    ($intern:ident, $i:expr) => {
        $intern::<String>::benchmarking_only_clear_interns();

        let mut interned_strings: Vec<$intern<String>> = Vec::new();
        for n in 0..100000 {
            interned_strings.push($intern::from_ref(memorable_wordlist::WORDS[($i + n) % 10]));
        }
    };
}

macro_rules! arena_few_strings {
    ($intern:ident, $i:expr) => {
        let arena: Arena<String> = Arena::new();

        let mut interned_strings: Vec<internment::ArenaIntern<String>> = Vec::new();
        for n in 0..100000 {
            interned_strings
                .push(arena.intern(memorable_wordlist::WORDS[($i + n) % 10].to_string()));
        }
    };
}

macro_rules! static_str {
    ($intern:ident, $i:expr) => {
        $intern::<&'static str>::benchmarking_only_clear_interns();

        let mut interned = Vec::new();
        for n in 0..100000 {
            interned.push($intern::new(
                memorable_wordlist::WORDS[($i + n) % memorable_wordlist::WORDS.len()],
            ));
        }
    };
}
macro_rules! arena_static_str {
    ($intern:ident, $i:expr) => {
        let arena: Arena<&'static str> = Arena::new();

        let mut interned = Vec::new();
        for n in 0..100000 {
            interned.push(
                arena.intern(memorable_wordlist::WORDS[($i + n) % memorable_wordlist::WORDS.len()]),
            );
        }
    };
}

/// Runs the workload on fifty threads at once, and waits for them all.
macro_rules! contended {
    ($intern:ident, $mac:ident) => {{
        let mut handles: Vec<std::thread::JoinHandle<()>> = Vec::new();
        for i in 0..50 {
            handles.push(std::thread::spawn(move || {
                $mac!($intern, i);
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
    }};
}

/// Runs the workload fifty times on the calling thread.
macro_rules! uncontended {
    ($intern:ident, $mac:ident) => {{
        for i in 0..50 {
            $mac!($intern, i);
        }
    }};
}

/// The two groups of a workload, with a candidate of each for every interner
/// that can run it, in a module of its own so that they can share names.
macro_rules! workload {
    ($m:ident, $mac:ident, $contended:literal, $uncontended:literal $(, $new:ident)? $(, arena $arena:ident)?) => {
        mod $m {
            use super::*;

            #[scaling::bench(group = $contended, name = "Intern", baseline)]
            fn contended_intern() {
                contended!(Intern, $mac)
            }
            $(
                // `$new` is only a marker that this workload has a `NewIntern`.
                #[scaling::bench(group = $contended, name = "NewIntern")]
                fn contended_new_intern() {
                    let _ = stringify!($new);
                    contended!(NewIntern, $mac)
                }
            )?
            #[scaling::bench(group = $contended, name = "ArcIntern")]
            fn contended_arc_intern() {
                contended!(ArcIntern, $mac)
            }
            #[scaling::bench(group = $contended, name = "Intern32")]
            fn contended_intern32() {
                contended!(Intern32, $mac)
            }

            #[scaling::bench(group = $uncontended, name = "Intern", baseline)]
            fn uncontended_intern() {
                uncontended!(Intern, $mac)
            }
            $(
                #[scaling::bench(group = $uncontended, name = "NewIntern")]
                fn uncontended_new_intern() {
                    let _ = stringify!($new);
                    uncontended!(NewIntern, $mac)
                }
            )?
            #[scaling::bench(group = $uncontended, name = "ArcIntern")]
            fn uncontended_arc_intern() {
                uncontended!(ArcIntern, $mac)
            }
            #[scaling::bench(group = $uncontended, name = "Intern32")]
            fn uncontended_intern32() {
                uncontended!(Intern32, $mac)
            }
            $(
                #[scaling::bench(group = $uncontended, name = "Arena")]
                fn uncontended_arena() {
                    uncontended!(Arena, $arena)
                }
            )?
        }
    };
}

workload!(static_str_, static_str, "static str contended", "static str uncontended", new_intern, arena arena_static_str);
workload!(few_strings_, few_strings, "few strings contended", "few strings uncontended", new_intern, arena arena_few_strings);
workload!(
    few_strings_from_,
    few_strings_from,
    "few strings from contended",
    "few strings from uncontended"
);
workload!(
    few_str_from_,
    few_str_from,
    "few str from contended",
    "few str from uncontended",
    new_intern
);
workload!(strings_, strings, "unique strings contended", "unique strings uncontended", new_intern, arena arena_strings);
workload!(
    four_types_,
    four_types,
    "four types contended",
    "four types uncontended",
    new_intern
);
workload!(
    same_arrays_,
    same_arrays,
    "same arrays contended",
    "same arrays uncontended",
    new_intern
);
workload!(
    different_arrays_,
    different_arrays,
    "different arrays contended",
    "different arrays uncontended",
    new_intern
);

fn main() -> Result<(), scaling::RegistrationError> {
    common::config(0.05, 120.0).run_and_print()
}
