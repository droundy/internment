use internment::{ArcIntern, Intern, LocalIntern};

fn main() {
    println!("^^^^^^^^^^^^^^^^^^^^^^");
    Intern::new(0i64);
    LocalIntern::new(0i64);
    ArcIntern::new(0i64);
    arc_interner::ArcIntern::new(0i64);
    let mut threads = Vec::new();
    for _ in 1..10000 {
        threads.push(std::thread::spawn(|| {
            ArcIntern::new(1i64);
        }));
        threads.push(std::thread::spawn(|| {
            let _x = ArcIntern::new(1i64);
            std::thread::sleep(std::time::Duration::from_nanos(1));
        }));
    }
    for x in threads.into_iter() {
        x.join().unwrap();
    }
    println!("vvvvvvvvvvvvvvvvvvvvv");
    println!("all good\n\n\n\n");
}
