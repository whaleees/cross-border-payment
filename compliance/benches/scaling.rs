use std::hint::black_box;
use std::time::{Duration, Instant};

use compliance::hash::compress;
use compliance::operator::{NullifierSet, Operator};
use compliance::params::{Params, ShuffleKey};
use compliance::paypay::{PayPay, User};
use compliance::shuffle::{Grid, ShuffleProof};
use compliance::verifier::Verifier;
use criterion::{BenchmarkId, Criterion, SamplingMode, criterion_group, criterion_main};
use curve25519_dalek::Scalar;
use curve25519_dalek::ristretto::CompressedRistretto;
use ed25519_dalek::SigningKey;
use ibc::commitment::{Commitment, random_blinding};
use ibc::params::PublicParams;
use rand_core::{OsRng, RngCore};

const CTX: &[u8] = b"round-000001";
const ANDI: User = 1;
const DAY: u32 = 20_741;

struct Shuffled {
    c_in: Vec<Commitment>,
    d_in: Vec<Commitment>,
    c_out: Vec<Commitment>,
    d_out: Vec<Commitment>,
    perm: Vec<usize>,
    delta: Vec<Scalar>,
    eta: Vec<Scalar>,
}

fn shuffled(pp: &PublicParams, n: usize) -> Shuffled {
    let c_in: Vec<Commitment> = (0..n).map(|_| Commitment(random_blinding() * pp.g_val + random_blinding() * pp.g_iden)).collect();
    let d_in: Vec<Commitment> = (0..n).map(|_| Commitment(random_blinding() * pp.g_val)).collect();
    let mut perm: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        perm.swap(i, (OsRng.next_u64() % (i as u64 + 1)) as usize);
    }
    let delta: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
    let eta: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
    let c_out = (0..n).map(|j| Commitment(c_in[perm[j]].0 + delta[j] * pp.g_ran)).collect();
    let d_out = (0..n).map(|j| Commitment(d_in[perm[j]].0 + eta[j] * pp.g_ran)).collect();
    Shuffled { c_in, d_in, c_out, d_out, perm, delta, eta }
}

// The shuffle on its own compresses its four lists inside every timed call; in a
// round they are compressed once and shared with stmt (decision 34).
fn encoded(s: &Shuffled) -> [Vec<CompressedRistretto>; 4] {
    [compress(&s.c_in), compress(&s.d_in), compress(&s.c_out), compress(&s.d_out)]
}

fn prove(pp: &PublicParams, key: &ShuffleKey, grid: Grid, s: &Shuffled) -> ShuffleProof {
    let enc = encoded(s);
    ShuffleProof::prove(key, pp, grid, &s.c_in, &s.d_in, &s.c_out, &s.d_out, enc.each_ref().map(Vec::as_slice), &s.perm, &s.delta, &s.eta, CTX)
}

fn verify(pp: &PublicParams, key: &ShuffleKey, grid: Grid, s: &Shuffled, p: &ShuffleProof) -> bool {
    let enc = encoded(s);
    p.verify(key, pp, grid, &s.c_in, &s.d_in, &s.c_out, &s.d_out, enc.each_ref().map(Vec::as_slice), CTX)
}

// The shuffle alone: by N at the protocol's grid, then by m at N = 1,000 (decision 18f).
fn shuffle(c: &mut Criterion) {
    let pp = Params::setup().pp;
    let mut cases: Vec<(usize, Grid)> = [100, 1_000, 10_000].iter().map(|&n| (n, Grid::for_len(n))).collect();
    cases.extend([1, 4, 32].iter().map(|&m| (1_000, Grid::with_rows(1_000, m))));

    let mut g = c.benchmark_group("shuffle");
    g.sample_size(10).sampling_mode(SamplingMode::Flat);
    for (n, grid) in cases {
        let s = shuffled(&pp, n);
        let key = ShuffleKey::new(&pp, grid.n);
        let p = prove(&pp, &key, grid, &s);
        assert!(verify(&pp, &key, grid, &s, &p));
        println!("shuffle N = {n}, grid {} x {}: proof {} bytes", grid.m, grid.n, p.size_bytes());

        let id = format!("n{n}_m{}", grid.m);
        g.bench_function(BenchmarkId::new("prove", &id), |b| b.iter(|| prove(&pp, &key, grid, black_box(&s))));
        g.bench_function(BenchmarkId::new("verify", &id), |b| b.iter(|| assert!(verify(&pp, &key, grid, &s, black_box(&p)))));
    }
    g.finish();
}

// Andi with n - 1 records and a state token, so the next payment has N = n:
// one first payment that brings in n - 2 domestic records.
fn history(n: usize) -> (PayPay, Verifier, NullifierSet) {
    let sk = SigningKey::generate(&mut OsRng);
    let mut op = Operator::new();
    op.register(1, sk.verifying_key(), u64::MAX / 4); // a limit nobody reaches here
    let signed = op.publish();
    let mut verifier = Verifier::new(1, sk, &signed, &op.public_key()).unwrap();
    let mut paypay = PayPay::new(&signed, &op.public_key()).unwrap();
    paypay.register(ANDI, b"Andi, passport TR0001234");
    for _ in 0..n.saturating_sub(2) {
        paypay.record_domestic(ANDI, 100, DAY - 1);
    }
    let tid = paypay.issue_tid(ANDI);
    let req = verifier.ask(tid, 100, DAY - 1);
    let pkg = paypay.respond(&req, DAY - 1).unwrap();
    let token = verifier.decide(&mut op.ns, &req.x.round_id, &pkg).unwrap();
    assert!(paypay.accept(&req.x.round_id, token));
    (paypay, verifier, op.ns)
}

// A whole round at N = n: PayPay building Phi (G3-G5), and the verifier deciding (G6-G7).
fn round(c: &mut Criterion) {
    let mut g = c.benchmark_group("round");
    g.sample_size(10).sampling_mode(SamplingMode::Flat);
    for n in [10, 100, 1_000] {
        let (paypay, verifier, ns) = history(n);

        // Size of one Phi at this N.
        {
            let (mut p, mut v) = (paypay.clone(), verifier.clone());
            let req = v.ask(p.issue_tid(ANDI), 100, DAY);
            let pkg = p.respond(&req, DAY).unwrap();
            assert_eq!(pkg.data.n(), n);
            println!("round N = {n}: Phi {} bytes, of which proofs {} bytes", pkg.size_bytes(), pkg.proofs.size_bytes());
        }

        g.bench_function(BenchmarkId::new("paypay_respond", n), |b| {
            b.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    let (mut p, mut v) = (paypay.clone(), verifier.clone());
                    let req = v.ask(p.issue_tid(ANDI), 100, DAY);
                    let start = Instant::now();
                    let pkg = p.respond(&req, DAY).unwrap();
                    total += start.elapsed();
                    black_box(pkg);
                }
                total
            })
        });

        g.bench_function(BenchmarkId::new("verifier_decide", n), |b| {
            b.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    let (mut p, mut v, mut set) = (paypay.clone(), verifier.clone(), ns.clone());
                    let req = v.ask(p.issue_tid(ANDI), 100, DAY);
                    let pkg = p.respond(&req, DAY).unwrap();
                    let start = Instant::now();
                    let token = v.decide(&mut set, &req.x.round_id, &pkg);
                    total += start.elapsed();
                    assert!(token.is_ok());
                }
                total
            })
        });
    }
    g.finish();
}

criterion_group!(benches, shuffle, round);
criterion_main!(benches);
