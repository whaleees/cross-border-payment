// Where the time of one round goes, step by step, at a given N:
//
//   cargo run --release --example breakdown -- 1000
//
// Each step is timed on its own, best of a few runs, with the same public functions
// the round calls, on a real package. The steps do not add up exactly to the whole
// round, which also copies lists and allocates.

use std::time::Instant;

use compliance::ctx::{BOTH, DATE, Round, STAGE_MIDEQ, STAGE_NEW_PAIR, STAGE_SHUFFLE, STAGE_TOTAL, VALUE};
use compliance::hash::compress;
use compliance::operator::{Entry, NullifierSet, Operator};
use compliance::package::{Package, Start, statement};
use compliance::params::{Params, ShuffleKey};
use compliance::paypay::{PayPay, User};
use compliance::range::{Opened, RangeKey, prove_amounts, verify_amounts};
use compliance::request::SignedRequest;
use compliance::shuffle::{Grid, ShuffleProof, multiexp};
use compliance::state_token::StateToken;
use compliance::verifier::Verifier;
use curve25519_dalek::ristretto::RistrettoBasepointTable;
use curve25519_dalek::traits::{MultiscalarMul, VartimeMultiscalarMul};
use curve25519_dalek::{RistrettoPoint, Scalar};
use ed25519_dalek::SigningKey;
use ibc::commitment::{Commitment, Opening, random_blinding};
use ibc::mideq::MIDEqProof;
use ibc::params::value_to_scalar;
use rand_core::OsRng;

const ANDI: User = 1;
const DAY: u32 = 20_741;
const REPS: usize = 5;

// Best of REPS runs, in seconds.
fn best<T>(mut f: impl FnMut() -> T) -> f64 {
    (0..REPS)
        .map(|_| {
            let t = Instant::now();
            std::hint::black_box(f());
            t.elapsed().as_secs_f64()
        })
        .fold(f64::MAX, f64::min)
}

fn print_rows(rows: &[(&str, f64)]) {
    for (name, secs) in rows {
        println!("  {name:<46}{:>9.2} ms", secs * 1e3);
    }
}

// Andi with n - 1 records and a token, as in benches/scaling.rs. Also returns the
// verifier's signing key, to time G7 on its own.
fn history(n: usize) -> (PayPay, Verifier, NullifierSet, SigningKey) {
    let sk = SigningKey::generate(&mut OsRng);
    let mut op = Operator::new();
    op.register(1, sk.verifying_key(), u64::MAX / 4);
    let signed = op.publish();
    let mut verifier = Verifier::new(1, sk.clone(), &signed, &op.public_key()).unwrap();
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
    (paypay, verifier, op.ns, sk)
}

fn fresh_round(paypay: &PayPay, verifier: &Verifier) -> (PayPay, Verifier, SignedRequest, Package) {
    let (mut p, mut v) = (paypay.clone(), verifier.clone());
    let req = v.ask(p.issue_tid(ANDI), 100, DAY);
    let pkg = p.respond(&req, DAY).unwrap();
    (p, v, req, pkg)
}

fn random_points(pp: &ibc::params::PublicParams, k: usize) -> Vec<RistrettoPoint> {
    (0..k).map(|_| random_blinding() * pp.g_val + random_blinding() * pp.g_iden).collect()
}

fn main() {
    let n: usize = std::env::args().nth(1).map(|a| a.parse().expect("N")).unwrap_or(1_000);
    let pp = Params::setup().pp;
    let (paypay, verifier, ns, sk) = history(n);
    let pk = sk.verifying_key();
    let (_, _, req, pkg) = fresh_round(&paypay, &verifier);
    let (x, d, pr) = (req.x, &pkg.data, &pkg.proofs);
    let Start::Token { token, rho, c_old, .. } = &d.start else { panic!("a later payment") };
    let enc = d.encode();
    let (ec_in, ed_in) = enc.inputs();
    let encoded = [&ec_in[..], &ed_in, &enc.c_out, &enc.d_out];
    let round = Round { round_id: x.round_id, stmt: statement(&x, d, &enc) };
    let grid = Grid::for_len(d.n());
    let key = ShuffleKey::new(&pp, grid.n);
    let range_key = RangeKey::new(&pp, 2);
    let (c_in, d_in) = d.inputs();
    println!("N = {}, grid {} x {}, e = {}\n", d.n(), grid.m, grid.n, d.e);

    // --- single operations, the unit of every estimate ---
    let pts = random_points(&pp, grid.len());
    let scalars: Vec<Scalar> = pts.iter().map(|_| random_blinding()).collect();
    let table = RistrettoBasepointTable::create(&pp.g_ran);
    let per = |secs: f64, count: usize| secs / count as f64 * 1e6;
    println!("ONE OPERATION");
    println!("  {:<46}{:>9.2} us", "point compression", per(best(|| pts.iter().map(|p| p.compress()).count()), pts.len()));
    println!("  {:<46}{:>9.2} us", "s*g_ran, variable base", per(best(|| scalars.iter().map(|s| s * pp.g_ran).count()), pts.len()));
    println!("  {:<46}{:>9.2} us", "s*g_ran, precomputed table", per(best(|| scalars.iter().map(|s| s * &table).count()), pts.len()));
    let ct_msm = |k: usize| per(best(|| RistrettoPoint::multiscalar_mul(&scalars[..k], &pts[..k])), k);
    println!("  {:<46}{:>9.2} us", format!("constant-time MSM, per point, size n = {}", grid.n), ct_msm(grid.n));
    println!("  {:<46}{:>9.2} us", format!("constant-time MSM, per point, size {}", grid.len()), ct_msm(grid.len()));
    // The verifier's large checks: one list of N, or all four lists at once.
    let many = random_points(&pp, 4 * grid.len());
    let many_s: Vec<Scalar> = many.iter().map(|_| random_blinding()).collect();
    let vt_msm = |k: usize| per(best(|| RistrettoPoint::vartime_multiscalar_mul(&many_s[..k], &many[..k])), k);
    println!("  {:<46}{:>9.2} us", format!("variable-time MSM, per point, size {}", grid.len()), vt_msm(grid.len()));
    println!("  {:<46}{:>9.2} us\n", format!("variable-time MSM, per point, size {}", many.len()), vt_msm(many.len()));

    // --- the verifier ---
    println!("VERIFIER (G6, G7)");
    let rows = [
        ("compress every list once", best(|| d.encode())),
        ("state token: hash + Ed25519 check", best(|| token.verify(&pk, &enc.c_old, &enc.d_old))),
        ("state token: open rho, look up nf", best(|| token.open(rho).map(|nf| ns.contains(&Entry::Nullifier(nf))))),
        ("stmt", best(|| statement(&x, d, &enc))),
        ("Pi.MIDEq verify (ibc; compresses its inputs)", best(|| {
            let cs: Vec<Commitment> = [x.tid].into_iter().chain(c_old.iter().chain(&d.c_dom).copied()).collect();
            pr.mideq.as_ref().unwrap().verify(&pp, &cs, &round.ctx(STAGE_MIDEQ, VALUE, 0))
        })),
        ("Pi.TxVer + Pi.FullEq verify", best(|| {
            let d_ref = Commitment(Scalar::from(x.t_now) * pp.g_val);
            pr.txver.verify(&pp, &x.tid, &d.c_tx, value_to_scalar(x.v), &round.ctx(STAGE_NEW_PAIR, VALUE, 0))
                && pr.fulleq.verify(&pp, &d.d_tx, &d_ref, &round.ctx(STAGE_NEW_PAIR, DATE, 0))
        })),
        ("front sum + Pi.VEq verify", best(|| {
            let front = d.front().0;
            let c_sum = front.iter().skip(1).fold(front[0], |acc, c| acc + *c);
            pr.sum.verify(&pp, &c_sum, &d.v_s, &round.ctx(STAGE_TOTAL, VALUE, 0))
        })),
        ("shuffle key (derive_generators)", best(|| ShuffleKey::new(&pp, grid.n))),
        ("shuffle verify", best(|| {
            let proof = pr.shuffle.as_ref().unwrap();
            proof.verify(&key, &pp, grid, &c_in, &d_in, &d.c_out, &d.d_out, encoded, &round.ctx(STAGE_SHUFFLE, BOTH, 0))
        })),
        ("amounts verify (Bulletproofs)", best(|| {
            verify_amounts(&range_key, &d.v_dom, &d.v_s, u64::MAX / 4, &pr.amounts, &round.ctx(STAGE_TOTAL, VALUE, 1))
        })),
        ("G7: sign the new front", best(|| {
            let (fc, fd) = enc.front(d.e);
            StateToken::issue(&sk, 1, fc, fd, d.cm_next)
        })),
    ];
    print_rows(&rows);
    let decide = (0..REPS)
        .map(|_| {
            let (_, mut v, req, pkg) = fresh_round(&paypay, &verifier);
            let mut set = ns.clone();
            let t = Instant::now();
            assert!(v.decide(&mut set, &req.x.round_id, &pkg).is_ok());
            t.elapsed().as_secs_f64()
        })
        .fold(f64::MAX, f64::min);
    print_rows(&[("sum of the steps", rows.iter().map(|r| r.1).sum()), ("whole decide", decide)]);

    // --- PayPay. The shuffle's secrets are PayPay's own, so the shuffle is timed on
    // fresh lists of the same N; the other steps on the package above. ---
    println!("\nPAYPAY (G3-G5)");
    let n_all = d.n();
    let deltas: Vec<Scalar> = (0..2 * n_all).map(|_| random_blinding()).collect();
    let s_in = (random_points(&pp, n_all), random_points(&pp, n_all));
    let perm: Vec<usize> = (0..n_all).rev().collect();
    let (delta, eta) = deltas.split_at(n_all);
    let s_c_in: Vec<Commitment> = s_in.0.iter().copied().map(Commitment).collect();
    let s_d_in: Vec<Commitment> = s_in.1.iter().copied().map(Commitment).collect();
    let s_c_out: Vec<Commitment> = (0..n_all).map(|j| Commitment(s_c_in[perm[j]].0 + delta[j] * pp.g_ran)).collect();
    let s_d_out: Vec<Commitment> = (0..n_all).map(|j| Commitment(s_d_in[perm[j]].0 + eta[j] * pp.g_ran)).collect();
    let s_enc = [compress(&s_c_in), compress(&s_d_in), compress(&s_c_out), compress(&s_d_out)];
    let rows_of = |v: &[RistrettoPoint]| grid.rows(v);
    let (c_rows, d_rows) = (rows_of(&pts), rows_of(&random_points(&pp, grid.len())));
    let b_rows = grid.rows(&scalars);
    let s_b: Vec<Scalar> = (0..grid.m).map(|_| random_blinding()).collect();
    let r = Round { round_id: [1; 32], stmt: [2; 32] };
    let rows = [
        ("compress every list once", best(|| d.encode())),
        ("re-randomise 2N outputs, variable base", best(|| deltas.iter().map(|s| s * pp.g_ran).count())),
        ("re-randomise 2N outputs, precomputed table", best(|| deltas.iter().map(|s| s * &table).count())),
        ("stmt", best(|| statement(&x, d, &enc))),
        ("Pi.MIDEq prove (ibc; timing only)", {
            let cs: Vec<Commitment> = [x.tid].into_iter().chain(c_old.iter().copied()).collect();
            let os: Vec<Opening> = cs.iter().map(|_| Opening { id: Scalar::ONE, val: Scalar::ONE, blinding: Scalar::ONE }).collect();
            best(|| MIDEqProof::prove(&pp, &cs, &os, &r.ctx(STAGE_MIDEQ, VALUE, 0)))
        }),
        ("shuffle key (derive_generators)", best(|| ShuffleKey::new(&pp, grid.n))),
        ("shuffle prove, S1-S6", best(|| {
            let e = s_enc.each_ref().map(Vec::as_slice);
            ShuffleProof::prove(&key, &pp, grid, &s_c_in, &s_d_in, &s_c_out, &s_d_out, e, &perm, delta, eta, b"ctx")
        })),
        ("  of which S6's diagonals (both lists)", best(|| {
            multiexp::commit(&key, &pp.g_ran, &c_rows, &d_rows, &b_rows, &s_b, Scalar::ONE, Scalar::ONE)
        })),
        ("amounts prove (Bulletproofs, 64 bit)", best(|| {
            let total = Opened { v: 1_000, blinding: Scalar::ONE };
            prove_amounts(&range_key, &[], &total, 1_000_000, &r.ctx(STAGE_TOTAL, VALUE, 1))
        })),
    ];
    print_rows(&rows);
    let respond = (0..REPS)
        .map(|_| {
            let (mut p, mut v) = (paypay.clone(), verifier.clone());
            let req = v.ask(p.issue_tid(ANDI), 100, DAY);
            let t = Instant::now();
            std::hint::black_box(p.respond(&req, DAY).unwrap());
            t.elapsed().as_secs_f64()
        })
        .fold(f64::MAX, f64::min);
    print_rows(&[("whole respond", respond)]);
}
