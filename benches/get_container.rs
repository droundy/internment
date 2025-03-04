//! This is a benchmark to demonstrate that cached types (`String`, `str` as of now)
//! are faster than non-cached types because the lack of getting container from a dashmap.
//!
//! The results show a whopping 26% performance gain for short `ArcIntern<String>`.

use criterion::*;
use internment::ArcIntern;

const ITER: usize = 200_000;
const RANGE: usize = 20_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct NewType<T>(T);

fn bench_get_container(c: &mut Criterion) {
    let mut group = c.benchmark_group("cached");
    let vals: Vec<_> = (0..RANGE).map(|idx| format!("short-{}", idx)).collect();

    // time:   [17.635 ms 17.707 ms 17.782 ms]
    group.bench_function(BenchmarkId::new("String", "short"), |b| {
        b.iter_batched(
            || {},
            |_| {
                let mut ans = Vec::with_capacity(ITER);
                for idx in 0..ITER {
                    let s = ArcIntern::<String>::new(vals[idx % RANGE].clone());
                    ans.push(s);
                }
            },
            criterion::BatchSize::PerIteration,
        );
    });
    group.bench_function(BenchmarkId::new("String", "short-from_ref"), |b| {
        b.iter_batched(
            || {},
            |_| {
                let mut ans = Vec::with_capacity(ITER);
                for idx in 0..ITER {
                    let s = ArcIntern::<String>::from_ref(&vals[idx % RANGE]);

                    ans.push(s);
                }
            },
            criterion::BatchSize::PerIteration,
        );
    });

    group.bench_function(BenchmarkId::new("String", "short-from_str"), |b| {
        b.iter_batched(
            || {},
            |_| {
                let mut ans = Vec::with_capacity(ITER);
                for idx in 0..ITER {
                    let s = ArcIntern::<String>::from_str(&vals[idx % RANGE]);

                    ans.push(s);
                }
            },
            criterion::BatchSize::PerIteration,
        );
    });
    group.finish();

    let new_vals: Vec<_> = (0..RANGE)
        .map(|idx| NewType(format!("short-{}", idx)))
        .collect();
    let mut group = c.benchmark_group("uncached");
    // time:   [22.209 ms 22.294 ms 22.399 ms] => that's 26% faster!
    group.bench_function(BenchmarkId::new("NewType<String>", "short"), |b| {
        b.iter_batched(
            || {},
            |_| {
                let mut ans = Vec::with_capacity(ITER);
                for idx in 0..ITER {
                    let s = ArcIntern::<NewType<String>>::new(new_vals[idx % RANGE].clone());
                    ans.push(s);
                }
            },
            criterion::BatchSize::PerIteration,
        );
    });
    // demonstrate that NewType does not affect performance
    // time:   [8.0247 ms 8.0419 ms 8.0607 ms]
    group.bench_function(BenchmarkId::new("usize", "short"), |b| {
        b.iter_batched(
            || {},
            |_| {
                let mut ans = Vec::with_capacity(ITER);
                for idx in 0..ITER {
                    let s = ArcIntern::<usize>::new(idx % RANGE);
                    ans.push(s);
                }
            },
            criterion::BatchSize::PerIteration,
        );
    });
    // time:   [8.0210 ms 8.0341 ms 8.0485 ms] => no changes! NewType does not affect performance.
    group.bench_function(BenchmarkId::new("NewType<usize>", "short"), |b| {
        b.iter_batched(
            || {},
            |_| {
                let mut ans = Vec::with_capacity(ITER);
                for idx in 0..ITER {
                    let s = ArcIntern::<NewType<usize>>::new(NewType(idx % RANGE));
                    ans.push(s);
                }
            },
            criterion::BatchSize::PerIteration,
        );
    });
    group.finish();
}

criterion_group!(benches, bench_get_container);
criterion_main!(benches);
