use easybench::{bench, bench_gen_env};

use internment::{ArcIntern, Intern, LocalIntern};

fn main() {
    Intern::new(0i64);
    LocalIntern::new(0i64);
    ArcIntern::new(0i64);
    for x in 0u8..=255 {
        Intern::new(x);
        LocalIntern::new(x);
        ArcIntern::new(x);
    }
    println!(
        "Intern<i64>::new {}",
        bench_gen_env(|| rand::random::<i64>(), |x| Intern::new(*x))
    );
    println!(
        "Intern<u8>::new {}",
        bench_gen_env(|| rand::random::<u8>(), |x| Intern::new(*x))
    );
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
    let i = arc_interner::ArcIntern::new(7i64);
    println!("arc_interner::ArcIntern<i64>::clone {}", bench(|| i.clone()));
    println!();
}
