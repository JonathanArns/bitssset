use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

use bitssset;

fn bitssset_bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("bitssset");
    type BS = bitssset::Bitset::<256>;
    group.bench_function("AND", |b| {
        let lhs = BS::with_bit_set(57);
        let rhs = BS::with_bit_set(67);
        b.iter(|| lhs & rhs)
    });
    group.bench_function("AND_ASSIGN", |b| {
        let mut lhs = BS::with_bit_set(57);
        let rhs = BS::with_bit_set(67);
        b.iter(|| {lhs &= rhs; lhs})
    });
    group.bench_function("OR", |b| {
        let lhs = BS::with_bit_set(57);
        let rhs = BS::with_bit_set(67);
        b.iter(|| lhs | rhs)
    });
    group.bench_function("OR_ASSIGN", |b| {
        let mut lhs = BS::with_bit_set(57);
        let rhs = BS::with_bit_set(67);
        b.iter(|| {lhs |= rhs; lhs})
    });
    group.bench_function("XOR", |b| {
        let lhs = BS::with_bit_set(57);
        let rhs = BS::with_bit_set(67);
        b.iter(|| lhs ^ rhs)
    });
    group.bench_function("XOR_ASSIGN", |b| {
        let mut lhs = BS::with_bit_set(57);
        let rhs = BS::with_bit_set(67);
        b.iter(|| {lhs ^= rhs; lhs})
    });
    group.bench_function("SHL", |b| {
        let mut set = BS::with_bit_set(57);
        set.set_bit(67);
        b.iter(|| set << 11)
    });
    group.bench_function("SHL_ASSIGN", |b| {
        let mut set = BS::with_bit_set(57);
        set.set_bit(67);
        b.iter(|| {set <<= 11; set})
    });
    group.bench_function("SHR", |b| {
        let mut set = BS::with_bit_set(57);
        set.set_bit(67);
        b.iter(|| set >> 11)
    });
    group.bench_function("SHR_ASSIGN", |b| {
        let mut set = BS::with_bit_set(57);
        set.set_bit(67);
        b.iter(|| {set >>= 11; set})
    });
}

criterion_group!(
    name = benches;
    config = Criterion::default()
        .warm_up_time(Duration::from_millis(3000))
        .measurement_time(Duration::from_millis(5000))
        .without_plots();
    targets = bitssset_bench
);
criterion_main!(benches);
