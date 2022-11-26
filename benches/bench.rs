#[cfg(feature = "bench")]
use scaling::{bench, bench_gen_env};
#[cfg(feature = "bench")]
use std::collections::HashSet;

#[cfg(feature = "bench")]
use internment::{ArcIntern, Arena, Intern, NewIntern};

#[cfg(not(feature = "bench"))]
fn main() {
    println!("Enable bench feature if you want a benchmark")
}

#[cfg(feature = "bench")]
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

#[cfg(feature = "bench")]
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

#[cfg(feature = "bench")]
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

#[cfg(feature = "bench")]
macro_rules! strings {
    ($intern:ident, $i:expr) => {
        $intern::<String>::benchmarking_only_clear_interns();

        let mut interned_strings = Vec::new();
        for n in 0..100000 {
            interned_strings.push($intern::new(format!("i {} and n {}", $i, n)));
        }
    };
}

#[cfg(feature = "bench")]
macro_rules! arena_strings {
    ($intern:ident, $i:expr) => {
        let arena: Arena<String> = Arena::new();

        let mut interned_strings = Vec::new();
        for n in 0..100000 {
            interned_strings.push(arena.intern(format!("i {} and n {}", $i, n)));
        }
    };
}

#[cfg(feature = "bench")]
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

#[cfg(feature = "bench")]
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

#[cfg(feature = "bench")]
macro_rules! few_strings_from {
    ($intern:ident, $i:expr) => {
        $intern::<String>::benchmarking_only_clear_interns();

        let mut interned_strings: Vec<$intern<String>> = Vec::new();
        for n in 0..100000 {
            interned_strings.push($intern::from_ref(memorable_wordlist::WORDS[($i + n) % 10]));
        }
    };
}

#[cfg(feature = "bench")]
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

#[cfg(feature = "bench")]
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
#[cfg(feature = "bench")]
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

#[cfg(feature = "bench")]
macro_rules! contended {
    ($intern:ident,$mac:ident) => {
        bench(|| {
            let mut handles: Vec<std::thread::JoinHandle<()>> = Vec::new();
            for i in 0..50 {
                handles.push(std::thread::spawn(move || {
                    $mac!($intern, i);
                }));
            }
            for h in handles {
                h.join().unwrap();
            }
        })
    };
}

#[cfg(feature = "bench")]
macro_rules! uncontended {
    ($intern:ident,$mac:ident) => {
        bench(|| {
            for i in 0..50 {
                $mac!($intern, i);
            }
        })
    };
}

#[cfg(feature = "bench")]
fn main() {
    println!(
        "  Contended &'static str Intern {}",
        contended!(Intern, static_str)
    );
    println!(
        "Uncontended &'static str Intern {}",
        uncontended!(Intern, static_str)
    );
    println!(
        "  Contended &'stati.. NewIntern {}",
        contended!(NewIntern, static_str)
    );
    println!(
        "Uncontended &'stati.. NewIntern {}",
        uncontended!(NewIntern, static_str)
    );
    println!(
        "  Contended &'stat... ArcIntern {}",
        contended!(ArcIntern, static_str)
    );
    println!(
        "Uncontended &'stat... ArcIntern {}",
        uncontended!(ArcIntern, static_str)
    );
    println!(
        "Uncontended &'st... ArenaIntern {}",
        uncontended!(ArenaIntern, arena_static_str)
    );
    println!("\n");

    println!(
        "  Contended few Strings Intern {}",
        contended!(Intern, few_strings)
    );
    println!(
        "Uncontended few Strings Intern {}",
        uncontended!(Intern, few_strings)
    );
    println!(
        "  Contended few S... NewIntern {}",
        contended!(NewIntern, few_strings)
    );
    println!(
        "Uncontended few S... NewIntern {}",
        uncontended!(NewIntern, few_strings)
    );
    println!(
        "  Contended few S... ArcIntern {}",
        contended!(ArcIntern, few_strings)
    );
    println!(
        "Uncontended few S... ArcIntern {}",
        uncontended!(ArcIntern, few_strings)
    );
    println!(
        "Uncontended few S..ArenaIntern {}",
        uncontended!(ArcIntern, arena_few_strings)
    );
    println!(
        "  Contended few Strings Intern::from {}",
        contended!(Intern, few_strings_from)
    );
    println!(
        "Uncontended few Strings Intern::from {}",
        uncontended!(Intern, few_strings_from)
    );
    println!(
        "  Contended few S... ArcIntern::from {}",
        contended!(ArcIntern, few_strings_from)
    );
    println!(
        "Uncontended few S... ArcIntern::from {}",
        uncontended!(ArcIntern, few_strings_from)
    );
    println!(
        "  Contended few str. Intern::from {}",
        contended!(Intern, few_str_from)
    );
    println!(
        "Uncontended few str. Intern::from {}",
        uncontended!(Intern, few_str_from)
    );
    println!(
        "  Contended few str. NewIntern::from {}",
        contended!(NewIntern, few_str_from)
    );
    println!(
        "Uncontended few str. NewIntern::from {}",
        uncontended!(NewIntern, few_str_from)
    );
    println!("\n");

    println!(
        "  Contended unique Strings Intern {}",
        contended!(Intern, strings)
    );
    println!(
        "Uncontended unique Strings Intern {}",
        uncontended!(Intern, strings)
    );
    println!(
        "  Contended unique S... NewIntern {}",
        contended!(NewIntern, strings)
    );
    println!(
        "Uncontended unique S... NewIntern {}",
        uncontended!(NewIntern, strings)
    );
    println!(
        "  Contended unique S... ArcIntern {}",
        contended!(ArcIntern, strings)
    );
    println!(
        "Uncontended unique S... ArcIntern {}",
        uncontended!(ArcIntern, strings)
    );
    println!(
        "Uncontended unique S..ArenaIntern {}",
        uncontended!(ArcIntern, arena_strings)
    );
    println!("\n");

    println!(
        "  Contended four types Intern {}",
        contended!(Intern, four_types)
    );
    println!(
        "Uncontended four types Intern {}",
        uncontended!(Intern, four_types)
    );
    println!(
        "  Contended four ...NewIntern {}",
        contended!(NewIntern, four_types)
    );
    println!(
        "Uncontended four ...NewIntern {}",
        uncontended!(NewIntern, four_types)
    );
    println!(
        "  Contended four ...ArcIntern {}",
        contended!(ArcIntern, four_types)
    );
    println!(
        "Uncontended four ...ArcIntern {}",
        uncontended!(ArcIntern, four_types)
    );
    println!("\n");

    println!(
        "Contended arrays Intern {}",
        contended!(Intern, same_arrays)
    );
    println!(
        "Uncontended  ... Intern {}",
        uncontended!(Intern, same_arrays)
    );
    println!(
        "Contended ... NewIntern {}",
        contended!(NewIntern, same_arrays)
    );
    println!(
        "Uncontended . NewIntern {}",
        uncontended!(NewIntern, same_arrays)
    );
    println!(
        "Contended ... ArcIntern {}",
        contended!(ArcIntern, same_arrays)
    );
    println!(
        "Uncontended . ArcIntern {}",
        uncontended!(ArcIntern, same_arrays)
    );
    println!("\n");

    println!(
        "Contended different arrays Intern {}",
        contended!(Intern, different_arrays)
    );
    println!(
        "Contended different arrays Intern {}",
        uncontended!(Intern, different_arrays)
    );
    println!(
        "Contended different ... NewIntern {}",
        contended!(NewIntern, different_arrays)
    );
    println!(
        "Contended different ... NewIntern {}",
        uncontended!(NewIntern, different_arrays)
    );
    println!(
        "Contended different ... ArcIntern {}",
        contended!(ArcIntern, different_arrays)
    );
    println!(
        "Contended different ... ArcIntern {}",
        uncontended!(ArcIntern, different_arrays)
    );
    println!("\n");

    Intern::new(0i64);
    ArcIntern::new(0i64);
    arc_interner::ArcIntern::new(0i64);
    let s1: HashSet<_> = (1..3000)
        .map(|i| format!("hello this is a pretty long string {:500}", i))
        .collect();
    let s_short: HashSet<_> = (1..3000).map(|i| format!("{}", i)).collect();
    let s2: HashSet<_> = (1..1000)
        .map(|i| format!("hello this is a pretty long string also {:500}", i))
        .collect();
    for x in 0u8..=255 {
        Intern::new(x);
        ArcIntern::new(x);
        arc_interner::ArcIntern::new(x);
    }

    {
        fn mkset(s: &mut HashSet<String>) -> HashSet<String> {
            let mut n = HashSet::new();
            for x in s.iter() {
                n.insert(x.clone());
            }
            n
        }
        mkset(&mut s1.clone());
        println!(
            "String::new short {}",
            bench_gen_env(|| s_short.clone(), mkset)
        );
        println!("String::new {}", bench_gen_env(|| s1.clone(), mkset));
        fn rmset(s: &mut (HashSet<String>, HashSet<String>)) {
            for x in s.1.iter() {
                s.0.remove(x);
            }
        }
        let s1: HashSet<_> = s1.clone();
        let s2: HashSet<_> = s2.clone();
        println!(
            "String::compare/hash {}",
            bench_gen_env(|| (s1.clone(), s2.clone()), rmset)
        );

        println!(
            "String sort {}",
            bench_gen_env(|| s1.iter().cloned().collect::<Vec<_>>(), |v| v.sort())
        );
        println!(
            "Box<String> sort {}",
            bench_gen_env(
                || s1.iter().map(|s| Box::new(s.clone())).collect::<Vec<_>>(),
                |v| v.sort()
            )
        );
        println!(
            "String any eq {}",
            bench_gen_env(
                || s1.iter().cloned().collect::<Vec<_>>(),
                |v| v.iter().any(|s| s == "hello this is a pretty long string")
            )
        );
        println!(
            "Box<String> any eq {}",
            bench_gen_env(
                || s1.iter().map(|s| Box::new(s.clone())).collect::<Vec<_>>(),
                |v| v
                    .iter()
                    .any(|s| s.as_str() == "hello this is a pretty long string")
            )
        );
    }
    println!();

    println!(
        "Intern<i64>::new {}",
        bench_gen_env(|| rand::random::<i64>(), |x| Intern::new(*x))
    );
    println!(
        "Intern<u8>::new {}",
        bench_gen_env(|| rand::random::<u8>(), |x| Intern::new(*x))
    );
    {
        fn mkset(s: &mut HashSet<String>) -> HashSet<Intern<String>> {
            let mut n = HashSet::new();
            for x in s.iter() {
                n.insert(Intern::new(x.clone()));
            }
            n
        }
        mkset(&mut s1.clone());
        fn mksetfrom(s: &mut HashSet<String>) -> HashSet<Intern<String>> {
            let mut n = HashSet::new();
            for x in s.iter() {
                n.insert(Intern::from_ref(x as &str));
            }
            n
        }
        println!(
            "Intern<String>::new short {}",
            bench_gen_env(|| s_short.clone(), mkset)
        );
        println!(
            "Intern<String>::new short {}",
            bench_gen_env(|| s_short.clone(), mkset)
        );
        println!(
            "Intern<String>::from short {}",
            bench_gen_env(|| s_short.clone(), mkset)
        );
        println!(
            "Intern<String>::new {}",
            bench_gen_env(|| s1.clone(), mkset)
        );
        println!(
            "Intern<String>::from {}",
            bench_gen_env(|| s1.clone(), mksetfrom)
        );
        fn rmset(s: &mut (HashSet<Intern<String>>, HashSet<Intern<String>>)) {
            for x in s.1.iter() {
                s.0.remove(x);
            }
        }
        fn rmset_str(s: &mut (HashSet<Intern<str>>, HashSet<Intern<str>>)) {
            for x in s.1.iter() {
                s.0.remove(x);
            }
        }
        let s1: HashSet<_> = s1.iter().cloned().map(|s| Intern::new(s)).collect();
        let s2: HashSet<_> = s2.iter().cloned().map(|s| Intern::new(s)).collect();
        let s1_str: HashSet<Intern<str>> =
            s1.iter().cloned().map(|s| From::from(s.as_str())).collect();
        let s2_str: HashSet<Intern<str>> =
            s2.iter().cloned().map(|s| From::from(s.as_str())).collect();
        println!(
            "Intern<String>::compare/hash {}",
            bench_gen_env(|| (s1.clone(), s2.clone()), rmset)
        );
        println!(
            "Intern<str>::compare/hash {}",
            bench_gen_env(|| (s1_str.clone(), s2_str.clone()), rmset_str)
        );

        println!(
            "Intern<String> sort {}",
            bench_gen_env(|| s1.iter().cloned().collect::<Vec<_>>(), |v| v.sort())
        );
        println!(
            "Intern<str> sort {}",
            bench_gen_env(
                || s1
                    .iter()
                    .map(|i| From::from(i.as_str()))
                    .collect::<Vec<Intern<str>>>(),
                |v| v.sort()
            )
        );
        println!(
            "Intern<String> any eq str {}",
            bench_gen_env(
                || s1.iter().cloned().collect::<Vec<_>>(),
                |v| v
                    .iter()
                    .any(|s| s.as_str() == "hello this is a pretty long string")
            )
        );
        let value = Intern::new("hello this is a pretty long string".to_string());
        println!(
            "Intern<String> any eq {}",
            bench_gen_env(
                || s1.iter().cloned().collect::<Vec<_>>(),
                |v| v.iter().any(|s| *s == value)
            )
        );
    }
    let i = Intern::new(7i64);
    println!("Intern<i64>::clone {}", bench(|| i.clone()));
    println!();

    println!(
        "ArcIntern<i64>::new {}",
        bench_gen_env(|| rand::random::<i64>(), |x| ArcIntern::new(*x))
    );
    println!(
        "ArcIntern<u8>::new {}",
        bench_gen_env(|| rand::random::<u8>(), |x| ArcIntern::new(*x))
    );
    {
        fn mkset(s: &mut HashSet<String>) -> HashSet<ArcIntern<String>> {
            let mut n = HashSet::new();
            for x in s.iter() {
                n.insert(ArcIntern::new(x.clone()));
            }
            n
        }
        mkset(&mut s1.clone());
        println!(
            "ArcIntern<String>::new short {}",
            bench_gen_env(|| s_short.clone(), mkset)
        );
        println!(
            "ArcIntern<String>::new {}",
            bench_gen_env(|| s1.clone(), mkset)
        );
        fn mksetfrom(s: &mut HashSet<String>) -> HashSet<ArcIntern<String>> {
            let mut n = HashSet::new();
            for x in s.iter() {
                n.insert(ArcIntern::from_ref(x as &str));
            }
            n
        }
        println!(
            "ArcIntern<String>::from {}",
            bench_gen_env(|| s1.clone(), mksetfrom)
        );
        fn rmset(s: &mut (HashSet<ArcIntern<String>>, HashSet<ArcIntern<String>>)) {
            for x in s.1.iter() {
                s.0.remove(x);
            }
        }
        let s1: HashSet<_> = s1.iter().cloned().map(|s| ArcIntern::new(s)).collect();
        let s2: HashSet<_> = s2.iter().cloned().map(|s| ArcIntern::new(s)).collect();
        println!(
            "ArcIntern<String>::compare/hash {}",
            bench_gen_env(|| (s1.clone(), s2.clone()), rmset)
        );
        println!(
            "ArcIntern<String> sort {}",
            bench_gen_env(|| s1.iter().cloned().collect::<Vec<_>>(), |v| v.sort())
        );
        let value = ArcIntern::new("hello this is a pretty long string".to_string());
        println!(
            "ArcIntern<String> any eq {}",
            bench_gen_env(
                || s1.iter().cloned().collect::<Vec<_>>(),
                |v| v.iter().any(|s| *s == value)
            )
        );
    }
    let i = ArcIntern::new(7i64);
    println!("ArcIntern<i64>::clone {}", bench(|| i.clone()));
    println!();

    println!(
        "arc_interner::ArcIntern<i64>::new {}",
        bench_gen_env(
            || rand::random::<i64>(),
            |x| arc_interner::ArcIntern::new(*x)
        )
    );
    println!(
        "arc_interner::ArcIntern<u8>::new {}",
        bench_gen_env(
            || rand::random::<u8>(),
            |x| arc_interner::ArcIntern::new(*x)
        )
    );
    {
        fn mkset(s: &mut HashSet<String>) -> HashSet<arc_interner::ArcIntern<String>> {
            let mut n = HashSet::new();
            for x in s.iter() {
                n.insert(arc_interner::ArcIntern::new(x.clone()));
            }
            n
        }
        mkset(&mut s1.clone());
        println!(
            "arc_interner::ArcIntern<String>::new short {}",
            bench_gen_env(|| s_short.clone(), mkset)
        );
        println!(
            "arc_interner::ArcIntern<String>::new {}",
            bench_gen_env(|| s1.clone(), mkset)
        );
        fn rmset(
            s: &mut (
                HashSet<arc_interner::ArcIntern<String>>,
                HashSet<arc_interner::ArcIntern<String>>,
            ),
        ) {
            for x in s.1.iter() {
                s.0.remove(x);
            }
        }
        let s1: HashSet<_> = s1
            .iter()
            .cloned()
            .map(|s| arc_interner::ArcIntern::new(s))
            .collect();
        let s2: HashSet<_> = s2
            .iter()
            .cloned()
            .map(|s| arc_interner::ArcIntern::new(s))
            .collect();
        println!(
            "arc_interner::ArcIntern<String>::compare/hash {}",
            bench_gen_env(|| (s1.clone(), s2.clone()), rmset)
        );
        println!(
            "arc_interner::ArcIntern<String> sort {}",
            bench_gen_env(|| s1.iter().cloned().collect::<Vec<_>>(), |v| v.sort())
        );
    }
    let i = arc_interner::ArcIntern::new(7i64);
    println!(
        "arc_interner::ArcIntern<i64>::clone {}",
        bench(|| i.clone())
    );
    println!();
}
