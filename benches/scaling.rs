use std::hint::black_box;
use std::time::Duration;

use criterion::{BenchmarkId, Criterion, SamplingMode, Throughput, criterion_group, criterion_main};
use ibc::batchver::{BatchItem, batch_verify};
use ibc::commitment::{Commitment, Opening, commit, random_blinding};
use ibc::ideq::IdEqProof;
use ibc::mideq::MIDEqProof;
use ibc::params::{PublicParams, hash_identity, value_to_scalar};

const CTX: &[u8] = b"tx-000001";

fn same_identity(pp: &PublicParams, n: usize) -> (Vec<Commitment>, Vec<Opening>) {
    let id = hash_identity(b"alice");
    let os: Vec<Opening> = (0..n as u64)
        .map(|k| Opening { id, val: value_to_scalar(100 + k), blinding: random_blinding() })
        .collect();
    (os.iter().map(|o| commit(pp, o)).collect(), os)
}

// Chart 1 (task b): Pi.MIDEq over n commitments vs n-1 separate Pi.IDEq proofs.
fn mideq_vs_ideq(c: &mut Criterion) {
    let pp = PublicParams::setup();
    let mut g = c.benchmark_group("mideq_vs_ideq");
    g.sample_size(10).sampling_mode(SamplingMode::Flat)
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(5));

    for n in [2usize, 5, 10, 50, 100, 500, 1000] {
        let (cs, os) = same_identity(&pp, n);
        let mp = MIDEqProof::prove(&pp, &cs, &os, CTX);
        let basic: Vec<IdEqProof> = (1..n)
            .map(|i| IdEqProof::prove(&pp, &cs[0], &cs[i], &os[0], &os[i], CTX))
            .collect();

        g.bench_function(BenchmarkId::new("mideq_prove", n), |b| {
            b.iter(|| MIDEqProof::prove(&pp, black_box(&cs), &os, CTX))
        });
        g.bench_function(BenchmarkId::new("mideq_verify", n), |b| {
            b.iter(|| assert!(black_box(&mp).verify(&pp, &cs, CTX)))
        });
        // Basic: one Π.IDEq for c1 vs ci, every i = 2..n.
        g.bench_function(BenchmarkId::new("basic_prove", n), |b| {
            b.iter(|| {
                (1..n).map(|i| IdEqProof::prove(&pp, &cs[0], &cs[i], &os[0], &os[i], black_box(CTX)))
                      .collect::<Vec<_>>()
            })
        });
        g.bench_function(BenchmarkId::new("basic_verify", n), |b| {
            b.iter(|| {
                for (k, q) in black_box(&basic).iter().enumerate() {
                    assert!(q.verify(&pp, &cs[0], &cs[k + 1], CTX));
                }
            })
        });
    }
    g.finish();
}

// Chart 2 (task c): one BatchVer call vs m individual Pi.IDEq verifications.
fn batchver_vs_individual(c: &mut Criterion) {
    let pp = PublicParams::setup();
    let id = hash_identity(b"alice");
    let mut g = c.benchmark_group("batchver_vs_individual");
    g.sample_size(10).sampling_mode(SamplingMode::Flat)
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(5));

    for m in [1usize, 10, 100, 1000, 10000] {
        let items: Vec<BatchItem> = (0..m as u64)
            .map(|j| {
                let o0 = Opening { id, val: value_to_scalar(j),     blinding: random_blinding() };
                let o1 = Opening { id, val: value_to_scalar(j + 1), blinding: random_blinding() };
                let (c0, c1) = (commit(&pp, &o0), commit(&pp, &o1));
                BatchItem { c0, c1, ctx: CTX, proof: IdEqProof::prove(&pp, &c0, &c1, &o0, &o1, CTX) }
            })
            .collect();

        g.throughput(Throughput::Elements(m as u64));
        g.bench_function(BenchmarkId::new("batch", m), |b| {
            b.iter(|| assert!(batch_verify(&pp, black_box(&items))))
        });
        g.bench_function(BenchmarkId::new("individual", m), |b| {
            b.iter(|| {
                for it in black_box(&items) {
                    assert!(it.proof.verify(&pp, &it.c0, &it.c1, it.ctx));
                }
            })
        });
    }
    g.finish();
}

criterion_group!(benches, mideq_vs_ideq, batchver_vs_individual);
criterion_main!(benches);
