use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::Rng;
use upcast_arithmetic::UpcastAdd;

fn criterion_benchmark(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    {
        let mut under_limit = c.benchmark_group("Under Limit");
        under_limit.bench_function("Raw u64 add", |b| {
            b.iter(|| {
                let a = rng.gen_range(0..(u64::MAX / 2 - 1));
                let b = rng.gen_range(0..(u64::MAX / 2 - 1));
                let _ = black_box(a + b);
            })
        });

        under_limit.bench_function("Raw u64 add mod", |b| {
            b.iter(|| {
                let a = rng.gen_range(0..(u64::MAX / 2 - 1));
                let b = rng.gen_range(0..(u64::MAX / 2 - 1));
                let modulo = rng.gen_range(0..=u64::MAX);
                let _ = black_box((a + b) % modulo);
            })
        });

        under_limit.bench_function("upcast u64 add", |b| {
            b.iter(|| {
                let a = rng.gen_range(0..(u64::MAX / 2 - 1));
                let b = rng.gen_range(0..(u64::MAX / 2 - 1));
                let _ = black_box(a.upcast_add(b));
            })
        });

        under_limit.bench_function("upcast u64 add mod", |b| {
            b.iter(|| {
                let a = rng.gen_range(0..(u64::MAX / 2 - 1));
                let b = rng.gen_range(0..(u64::MAX / 2 - 1));
                let modulo = rng.gen_range(0..=u64::MAX);
                let _ = black_box(a.upcast_add_mod(b, modulo));
            })
        });
    }
    {
        let mut over_limit = c.benchmark_group("Over limit");
        over_limit.bench_function("Raw u64 -> u128 add", |b| {
            b.iter(|| {
                let a = rng.gen::<u64>() as u128;
                let b = rng.gen::<u64>() as u128;
                let _ = black_box(a + b);
            })
        });
        over_limit.bench_function("Raw u64 -> u128 add mod", |b| {
            b.iter(|| {
                let a = rng.gen::<u64>() as u128;
                let b = rng.gen::<u64>() as u128;
                let modulo = rng.gen::<u64>() as u128;
                let _ = black_box((a + b) % modulo);
            })
        });
        over_limit.bench_function("upcast u64 add", |b| {
            b.iter(|| {
                let a = rng.gen::<u64>();
                let b = rng.gen::<u64>();
                let _ = black_box(a.upcast_add(b));
            })
        });
        over_limit.bench_function("upcast u64 add mod", |b| {
            b.iter(|| {
                let a = rng.gen::<u64>();
                let b = rng.gen::<u64>();
                let modulo = rng.gen::<u64>();
                let _ = black_box(a.upcast_add_mod(b, modulo));
            })
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
