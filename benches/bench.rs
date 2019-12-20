use easybench::{bench_gen_env};

use internment::{Intern, LocalIntern, ArcIntern};

fn main() {
    Intern::new(0i64);
    LocalIntern::new(0i64);
    ArcIntern::new(0i64);
    for x in 0u8..=255 {
        Intern::new(x);
        LocalIntern::new(x);
        ArcIntern::new(x);
    }
    println!("Intern: {}",
             bench_gen_env(|| rand::random::<i64>(), |x| Intern::new(*x)));
    println!("Intern: {}",
             bench_gen_env(|| rand::random::<u8>(), |x| Intern::new(*x)));
    println!("LocalIntern: {}",
             bench_gen_env(|| rand::random::<i64>(), |x| LocalIntern::new(*x)));
    println!("LocalIntern: {}",
             bench_gen_env(|| rand::random::<u8>(), |x| LocalIntern::new(*x)));

    println!("ArcIntern: {}",
             bench_gen_env(|| rand::random::<i64>(), |x| ArcIntern::new(*x)));
    println!("ArcIntern: {}",
             bench_gen_env(|| rand::random::<u8>(), |x| ArcIntern::new(*x)));
}
