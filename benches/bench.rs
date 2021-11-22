#[cfg(feature = "bench")]
use scaling::{bench, bench_gen_env};
#[cfg(feature = "bench")]
use std::collections::HashSet;

#[cfg(feature = "bench")]
use internment::{ArcIntern, Intern, LocalIntern};

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
                    $intern::new([size+$i; 1000]);
                }
                1 => {
                    $intern::new([size+$i; 20]);
                }
                2 => {
                    $intern::new([size+$i; 30]);
                }
                3 => {
                    $intern::new([size+$i; 40]);
                }
                4 => {
                    $intern::new([size+$i; 50]);
                }
                5 => {
                    $intern::new([size+$i; 60]);
                }
                6 => {
                    $intern::new([size+$i; 70]);
                }
                7 => {
                    $intern::new([size+$i; 80]);
                }
                8 => {
                    $intern::new([size+$i; 90]);
                }
                _ => {
                    $intern::new([size+$i; 100]);
                }
            }
        }
    };
}

#[cfg(feature = "bench")]
macro_rules! contended {
    ($intern:ident,$mac:ident) => {
        bench(|| {
            let mut handles: Vec<std::thread::JoinHandle<()>> = Vec::new();
            for i in 0..50 {
                handles.push(std::thread::spawn(move || { $mac!($intern, i); }));
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
    println!("Contended Intern {} / {}",      contended!(Intern, four_types), uncontended!(Intern, four_types));
    println!("Contended ArcIntern {} / {}",   contended!(ArcIntern, four_types), uncontended!(ArcIntern, four_types));
    println!("Contended LocalIntern {} / {}", contended!(LocalIntern, four_types), uncontended!(LocalIntern, four_types));
    println!("\n");

    println!("Contended arrays Intern {} / {}",      contended!(Intern, same_arrays), uncontended!(Intern, same_arrays));
    println!("Contended arrays ArcIntern {} / {}",   contended!(ArcIntern, same_arrays), uncontended!(ArcIntern, same_arrays));
    println!("Contended arrays LocalIntern {} / {}", contended!(LocalIntern, same_arrays), uncontended!(LocalIntern, same_arrays));
    println!("\n");

    println!("Contended different arrays Intern {} / {}",      contended!(Intern, different_arrays), uncontended!(Intern, different_arrays));
    println!("Contended different arrays ArcIntern {} / {}",   contended!(ArcIntern, different_arrays), uncontended!(ArcIntern, different_arrays));
    println!("Contended different arrays LocalIntern {} / {}", contended!(LocalIntern, different_arrays), uncontended!(LocalIntern, different_arrays));
    println!("\n");

    Intern::new(0i64);
    LocalIntern::new(0i64);
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
        LocalIntern::new(x);
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
                n.insert(Intern::from(x as &str));
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
        let s1: HashSet<_> = s1.iter().cloned().map(|s| Intern::new(s)).collect();
        let s2: HashSet<_> = s2.iter().cloned().map(|s| Intern::new(s)).collect();
        println!(
            "Intern<String>::compare/hash {}",
            bench_gen_env(|| (s1.clone(), s2.clone()), rmset)
        );

        println!(
            "Intern<String> sort {}",
            bench_gen_env(|| s1.iter().cloned().collect::<Vec<_>>(), |v| v.sort())
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
        "LocalIntern<i64>::new {}",
        bench_gen_env(|| rand::random::<i64>(), |x| LocalIntern::new(*x))
    );
    println!(
        "LocalIntern<u8>::new {}",
        bench_gen_env(|| rand::random::<u8>(), |x| LocalIntern::new(*x))
    );
    {
        fn mkset(s: &mut HashSet<String>) -> HashSet<LocalIntern<String>> {
            let mut n = HashSet::new();
            for x in s.iter() {
                n.insert(LocalIntern::new(x.clone()));
            }
            n
        }
        mkset(&mut s1.clone());
        println!(
            "LocalIntern<String>::new short {}",
            bench_gen_env(|| s_short.clone(), mkset)
        );
        println!(
            "LocalIntern<String>::new {}",
            bench_gen_env(|| s1.clone(), mkset)
        );
        fn mksetfrom(s: &mut HashSet<String>) -> HashSet<LocalIntern<String>> {
            let mut n = HashSet::new();
            for x in s.iter() {
                n.insert(LocalIntern::from(x as &str));
            }
            n
        }
        println!(
            "LocalIntern<String>::from {}",
            bench_gen_env(|| s1.clone(), mksetfrom)
        );
        fn rmset(s: &mut (HashSet<LocalIntern<String>>, HashSet<LocalIntern<String>>)) {
            for x in s.1.iter() {
                s.0.remove(x);
            }
        }
        let s1: HashSet<_> = s1.iter().cloned().map(|s| LocalIntern::new(s)).collect();
        let s2: HashSet<_> = s2.iter().cloned().map(|s| LocalIntern::new(s)).collect();
        println!(
            "LocalIntern<String>::compare/hash {}",
            bench_gen_env(|| (s1.clone(), s2.clone()), rmset)
        );
        println!(
            "LocalIntern<String> sort {}",
            bench_gen_env(|| s1.iter().cloned().collect::<Vec<_>>(), |v| v.sort())
        );
        let value = LocalIntern::new("hello this is a pretty long string".to_string());
        println!(
            "LocalIntern<String> any eq {}",
            bench_gen_env(
                || s1.iter().cloned().collect::<Vec<_>>(),
                |v| v.iter().any(|s| *s == value)
            )
        );
    }
    let i = LocalIntern::new(7i64);
    println!("LocalIntern<i64>::clone {}", bench(|| i.clone()));
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
                n.insert(ArcIntern::from(x as &str));
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
