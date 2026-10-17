use std::hint::black_box;

use compliance::hash::compress;
use compliance::params::{Params, ShuffleKey};
use compliance::range::{Opened, RangeKey, prove_amounts, prove_expired, verify_amounts, verify_expired};
use compliance::shuffle::{Grid, ShuffleProof};
use compliance::state_token::{StateToken, fresh_preimage, nullifier_commitment};
use compliance::tag::{TagProof, tag};
use criterion::{Criterion, criterion_group, criterion_main};
use curve25519_dalek::Scalar;
use ed25519_dalek::SigningKey;
use ibc::commitment::{Commitment, Opening, commit, random_blinding};
use ibc::params::{hash_identity, value_to_scalar};
use rand_core::OsRng;

const CTX: &[u8] = b"round-000001";
const THETA: u64 = 20_377;

// One prove and one verify per component, at the sizes of a small round. A component
// on its own compresses its lists inside the timed call; within a round the lists are
// compressed once and shared (decision 34), which the round benchmark shows.
fn components(c: &mut Criterion) {
    // Fixtures built once, outside the timed loops.
    let params = Params::setup();
    let pp = params.pp;
    let id = hash_identity(b"alice");
    let o_tid = Opening { id, val: Scalar::ZERO, blinding: random_blinding() };
    let tid = commit(&pp, &o_tid);
    let t = tag(&params, &id);

    let mut g = c.benchmark_group("components");

    // Pi.Tag -- first payment only.
    let pt = TagProof::prove(&params, &tid, &t, &o_tid, CTX);
    g.bench_function("tag_prove", |b| b.iter(|| TagProof::prove(&params, &tid, &t, &o_tid, black_box(CTX))));
    g.bench_function("tag_verify", |b| b.iter(|| assert!(black_box(&pt).verify(&params, &tid, &t, CTX))));

    // State token over a list of 10 pairs.
    let sk = SigningKey::generate(&mut OsRng);
    let cs: Vec<Commitment> = (0..10).map(|_| commit(&pp, &Opening { id, val: value_to_scalar(100), blinding: random_blinding() })).collect();
    let ds: Vec<Commitment> = (0..10).map(|_| Commitment(random_blinding() * pp.g_ran)).collect();
    let cm = nullifier_commitment(&fresh_preimage());
    let token = StateToken::issue(&sk, 1, &compress(&cs), &compress(&ds), cm);
    g.bench_function("state_token_issue_n10", |b| b.iter(|| StateToken::issue(&sk, 1, &compress(black_box(&cs)), &compress(&ds), cm)));
    g.bench_function("state_token_verify_n10", |b| {
        b.iter(|| assert!(black_box(&token).verify(&sk.verifying_key(), &compress(&cs), &compress(&ds))))
    });

    // Bulletproofs: two expired dates (16 bits), and S, B - S with no domestic record (64 bits).
    let key = RangeKey::new(&pp, 2);
    let tail: Vec<Opened> = [20_000u64, 20_100].iter().map(|&t| Opened { v: t, blinding: random_blinding() }).collect();
    let tail_c: Vec<Commitment> = tail.iter().map(|d| Commitment(Scalar::from(d.v) * pp.g_val + d.blinding * pp.g_ran)).collect();
    let pe = prove_expired(&key, THETA, &tail, CTX).unwrap();
    g.bench_function("expiry_e2_prove", |b| b.iter(|| prove_expired(&key, THETA, black_box(&tail), CTX)));
    g.bench_function("expiry_e2_verify", |b| b.iter(|| assert!(verify_expired(&key, THETA, black_box(&tail_c), &pe, CTX))));

    let total = Opened { v: 40_000, blinding: random_blinding() };
    let v_s = Commitment(Scalar::from(total.v) * pp.g_val + total.blinding * pp.g_ran);
    let pa = prove_amounts(&key, &[], &total, 500_000, CTX).unwrap();
    g.bench_function("amounts_k0_prove", |b| b.iter(|| prove_amounts(&key, &[], black_box(&total), 500_000, CTX)));
    g.bench_function("amounts_k0_verify", |b| b.iter(|| assert!(verify_amounts(&key, &[], black_box(&v_s), 500_000, &pa, CTX))));

    // The shuffle at N = 100 (grid 10 x 10); scaling.rs sweeps N and m.
    let n = 100;
    let grid = Grid::for_len(n);
    let skey = ShuffleKey::new(&pp, grid.n);
    let c_in: Vec<Commitment> = (0..n).map(|_| Commitment(random_blinding() * pp.g_val + random_blinding() * pp.g_iden)).collect();
    let d_in: Vec<Commitment> = (0..n).map(|_| Commitment(random_blinding() * pp.g_val)).collect();
    let perm: Vec<usize> = (0..n).rev().collect();
    let delta: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
    let eta: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
    let c_out: Vec<Commitment> = (0..n).map(|j| Commitment(c_in[perm[j]].0 + delta[j] * pp.g_ran)).collect();
    let d_out: Vec<Commitment> = (0..n).map(|j| Commitment(d_in[perm[j]].0 + eta[j] * pp.g_ran)).collect();
    let encoded = || [compress(&c_in), compress(&d_in), compress(&c_out), compress(&d_out)];
    let prove = || {
        let enc = encoded();
        ShuffleProof::prove(&skey, &pp, grid, &c_in, &d_in, &c_out, &d_out, enc.each_ref().map(Vec::as_slice), &perm, &delta, &eta, CTX)
    };
    let ps = prove();
    g.bench_function("shuffle_n100_prove", |b| b.iter(|| black_box(prove())));
    g.bench_function("shuffle_n100_verify", |b| {
        b.iter(|| {
            let enc = encoded();
            assert!(black_box(&ps).verify(&skey, &pp, grid, &c_in, &d_in, &c_out, &d_out, enc.each_ref().map(Vec::as_slice), CTX))
        })
    });

    g.finish();
}

criterion_group!(benches, components);
criterion_main!(benches);
