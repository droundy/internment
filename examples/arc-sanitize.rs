use internment::{ArcIntern, Intern, LocalIntern};

fn main() {
    Intern::new(0i64);
    LocalIntern::new(0i64);
    ArcIntern::new(0i64);
    arc_interner::ArcIntern::new(0i64);
    for _ in 1..10000 {
        std::thread::spawn(|| {
            ArcIntern::new(1);
        });
    }
    println!("all good");
}
