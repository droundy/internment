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
fn main() {
    println!(
        "Contended Intern {}",
        bench(|| {
            let mut handles: Vec<std::thread::JoinHandle<()>> = Vec::new();
            for i in 0..50 {
                handles.push(std::thread::spawn(move || {
                    let mut interned_strings = Vec::new();
                    let mut interned_ints = Vec::new();
                    let mut interned_pairs = Vec::new();
                    let mut interned_triples = Vec::new();
                    for n in 0..100000 {
                        match (i + n) % 4 {
                            0 => {
                                interned_strings.push(Intern::new(format!("i {} and n {}", i, n)));
                            }
                            1 => {
                                interned_ints.push(Intern::new(i * n * 137));
                            }
                            2 => {
                                interned_pairs.push(Intern::new((i, n)));
                            }
                            _ => {
                                interned_triples.push(Intern::new((i, n, i + n)));
                            }
                        }
                    }
                }));
            }
            for h in handles {
                h.join().unwrap();
            }
        })
    );
    println!(
        "Contended ArcIntern {}",
        bench(|| {
            let mut handles: Vec<std::thread::JoinHandle<()>> = Vec::new();
            for i in 0..50 {
                handles.push(std::thread::spawn(move || {
                    let mut interned_strings = Vec::new();
                    let mut interned_ints = Vec::new();
                    let mut interned_pairs = Vec::new();
                    let mut interned_triples = Vec::new();
                    for n in 0..100000 {
                        match (i + n) % 4 {
                            0 => {
                                interned_strings.push(ArcIntern::new(format!("i {} and n {}", i, n)));
                            }
                            1 => {
                                interned_ints.push(ArcIntern::new(i * n * 137));
                            }
                            2 => {
                                interned_pairs.push(ArcIntern::new((i, n)));
                            }
                            _ => {
                                interned_triples.push(ArcIntern::new((i, n, i + n)));
                            }
                        }
                    }
                }));
            }
            for h in handles {
                h.join().unwrap();
            }
        })
    );
    println!(
        "Contended LocalIntern {} (not really contended)",
        bench(|| {
            let mut handles: Vec<std::thread::JoinHandle<()>> = Vec::new();
            for i in 0..50 {
                handles.push(std::thread::spawn(move || {
                    let mut interned_strings = Vec::new();
                    let mut interned_ints = Vec::new();
                    let mut interned_pairs = Vec::new();
                    let mut interned_triples = Vec::new();
                    for n in 0..100000 {
                        match (i + n) % 4 {
                            0 => {
                                interned_strings.push(LocalIntern::new(format!("i {} and n {}", i, n)));
                            }
                            1 => {
                                interned_ints.push(LocalIntern::new(i * n * 137));
                            }
                            2 => {
                                interned_pairs.push(LocalIntern::new((i, n)));
                            }
                            _ => {
                                interned_triples.push(LocalIntern::new((i, n, i + n)));
                            }
                        }
                    }
                }));
            }
            for h in handles {
                h.join().unwrap();
            }
        })
    );
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
