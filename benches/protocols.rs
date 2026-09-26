use std::hint::black_box;

use criterion::{Criterion, criterion_group, criterion_main};
use ibc::commitment::{Opening, commit, random_blinding};
use ibc::params::{PublicParams, hash_identity, value_to_scalar};

fn protocols(c: &mut Criterion) {
    // Fixtures built ONCE, outside the timed loop.
    let pp = PublicParams::setup();
    let o = Opening {
        id: hash_identity(b"alice"),
        val: value_to_scalar(1_500),
        blinding: random_blinding(),
    };

    c.bench_function("commit", |b| b.iter(|| commit(&pp, black_box(&o))));
}

criterion_group!(benches, protocols);
criterion_main!(benches);
