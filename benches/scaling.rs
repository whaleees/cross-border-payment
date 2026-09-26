use criterion::{Criterion, criterion_group, criterion_main};

fn scaling(_c: &mut Criterion) {}

criterion_group!(benches, scaling);
criterion_main!(benches);
