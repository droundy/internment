fn main() {
    let mut numbers = std::collections::HashSet::new();
    for _ in 0..500 {
        for i in 0..1000000 {
            numbers.insert(internment::ArcIntern::new(i));
        }
    }
}
