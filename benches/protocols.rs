use std::hint::black_box;

use criterion::{Criterion, criterion_group, criterion_main};
use ibc::commitment::{Opening, commit, random_blinding};
use ibc::fulleq::FullEqProof;
use ibc::ideq::IdEqProof;
use ibc::mideq::MIDEqProof;
use ibc::params::{PublicParams, hash_identity, value_to_scalar};
use ibc::txver::TxVerProof;
use ibc::veq::VEqProof;
use ibc::vver::VVerProof;

const CTX: &[u8] = b"tx-000001";

fn protocols(c: &mut Criterion) {
    // Fixtures built ONCE, outside the timed loops.
    let pp = PublicParams::setup();
    let id = hash_identity(b"alice");
    let v = value_to_scalar(1_500);

    // alice's registration commitment, and one transaction commitment.
    let o_ref = Opening { id, val: value_to_scalar(0), blinding: random_blinding() };
    let o_tx = Opening { id, val: v, blinding: random_blinding() };
    let c_ref = commit(&pp, &o_ref);
    let c_tx = commit(&pp, &o_tx);

    // bob receives the same value (for Pi.VEq: same value, different identity).
    let o_bob = Opening { id: hash_identity(b"bob"), val: v, blinding: random_blinding() };
    let c_bob = commit(&pp, &o_bob);

    // a re-randomisation of c_tx (for Pi.FullEq).
    let o_rr = Opening { blinding: o_tx.blinding + random_blinding(), ..o_tx };
    let c_rr = commit(&pp, &o_rr);

    // n = 10 of alice's commitments (for Pi.MIDEq at a fixed n; step 05 sweeps n).
    let os: Vec<Opening> = (0..10u64)
        .map(|k| Opening { id, val: value_to_scalar(100 + k), blinding: random_blinding() })
        .collect();
    let cs: Vec<_> = os.iter().map(|o| commit(&pp, o)).collect();

    let mut g = c.benchmark_group("protocols");

    g.bench_function("commit", |b| b.iter(|| commit(&pp, black_box(&o_tx))));

    // Pi.IDEq -- c_ref and c_tx share alice's identity.
    let pi = IdEqProof::prove(&pp, &c_ref, &c_tx, &o_ref, &o_tx, CTX);
    g.bench_function("ideq_prove", |b| {
        b.iter(|| IdEqProof::prove(&pp, &c_ref, &c_tx, &o_ref, &o_tx, black_box(CTX)))
    });
    g.bench_function("ideq_verify", |b| {
        b.iter(|| assert!(black_box(&pi).verify(&pp, &c_ref, &c_tx, CTX)))
    });

    // Pi.VVer -- c_tx holds the public value v.
    let pv = VVerProof::prove(&pp, &c_tx, v, &o_tx, CTX);
    g.bench_function("vver_prove", |b| {
        b.iter(|| VVerProof::prove(&pp, &c_tx, v, &o_tx, black_box(CTX)))
    });
    g.bench_function("vver_verify", |b| {
        b.iter(|| assert!(black_box(&pv).verify(&pp, &c_tx, v, CTX)))
    });

    // Pi.VEq -- c_tx and c_bob hold the same hidden value.
    let pe = VEqProof::prove(&pp, &c_tx, &c_bob, &o_tx, &o_bob, CTX);
    g.bench_function("veq_prove", |b| {
        b.iter(|| VEqProof::prove(&pp, &c_tx, &c_bob, &o_tx, &o_bob, black_box(CTX)))
    });
    g.bench_function("veq_verify", |b| {
        b.iter(|| assert!(black_box(&pe).verify(&pp, &c_tx, &c_bob, CTX)))
    });

    // Pi.FullEq -- c_rr is a re-randomisation of c_tx.
    let pf = FullEqProof::prove(&pp, &c_tx, &c_rr, &o_tx, &o_rr, CTX);
    g.bench_function("fulleq_prove", |b| {
        b.iter(|| FullEqProof::prove(&pp, &c_tx, &c_rr, &o_tx, &o_rr, black_box(CTX)))
    });
    g.bench_function("fulleq_verify", |b| {
        b.iter(|| assert!(black_box(&pf).verify(&pp, &c_tx, &c_rr, CTX)))
    });

    // Pi.TxVer -- c_tx has c_ref's identity AND holds v, under one challenge.
    let pt = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, CTX);
    g.bench_function("txver_prove", |b| {
        b.iter(|| TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, black_box(CTX)))
    });
    g.bench_function("txver_verify", |b| {
        b.iter(|| assert!(black_box(&pt).verify(&pp, &c_ref, &c_tx, v, CTX)))
    });

    // Pi.MIDEq -- all ten of alice's commitments share one identity.
    let pm = MIDEqProof::prove(&pp, &cs, &os, CTX);
    g.bench_function("mideq_n10_prove", |b| {
        b.iter(|| MIDEqProof::prove(&pp, black_box(&cs), &os, CTX))
    });
    g.bench_function("mideq_n10_verify", |b| {
        b.iter(|| assert!(black_box(&pm).verify(&pp, &cs, CTX)))
    });

    // Task (d) -- the Basic way: the same two facts as Pi.TxVer, as two independent
    // proofs (pi and pv from above).
    g.bench_function("basic_tx_prove", |b| {
        b.iter(|| {
            let a = IdEqProof::prove(&pp, &c_ref, &c_tx, &o_ref, &o_tx, black_box(CTX));
            let b = VVerProof::prove(&pp, &c_tx, v, &o_tx, black_box(CTX));
            (a, b)
        })
    });
    g.bench_function("basic_tx_verify", |b| {
        b.iter(|| {
            assert!(black_box(&pi).verify(&pp, &c_ref, &c_tx, CTX));
            assert!(black_box(&pv).verify(&pp, &c_tx, v, CTX));
        })
    });

    g.finish();

    // Throughput, end to end: commit a transaction, prove Pi.TxVer, verify it.
    // (Table 3.1's headline TPS is 1 / txver_verify and 1 / basic_tx_verify above.)
    let mut t = c.benchmark_group("tps");
    t.bench_function("transaction", |b| {
        b.iter(|| {
            let c_tx = commit(&pp, black_box(&o_tx));
            let p = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, CTX);
            assert!(p.verify(&pp, &c_ref, &c_tx, v, CTX));
        })
    });
    t.finish();
}

criterion_group!(benches, protocols);
criterion_main!(benches);
