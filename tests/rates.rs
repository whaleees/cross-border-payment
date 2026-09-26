use curve25519_dalek::Scalar;
use rand_core::{OsRng, RngCore};

use ibc::batchver::{BatchItem, batch_verify};
use ibc::commitment::{Commitment, Opening, commit, random_blinding};
use ibc::fulleq::FullEqProof;
use ibc::ideq::IdEqProof;
use ibc::mideq::MIDEqProof;
use ibc::params::{PublicParams, value_to_scalar};
use ibc::txver::TxVerProof;
use ibc::veq::VEqProof;
use ibc::vver::VVerProof;

const CTX: &[u8] = b"tx-000001";
const OTHER_CTX: &[u8] = b"tx-000002";

// Runs per scenario: RATES_N if set (e.g. RATES_N=200 while editing), else 10 000.
fn runs() -> usize {
    std::env::var("RATES_N").ok().and_then(|s| s.parse().ok()).unwrap_or(10_000)
}

fn random_id() -> Scalar {
    Scalar::random(&mut OsRng)
}

// A fresh opening: the given identity, a random amount, a random blinding.
fn opening(id: Scalar) -> Opening {
    Opening { id, val: value_to_scalar(OsRng.next_u64() % 1_000_000), blinding: random_blinding() }
}

// How many of n runs the verifier ACCEPTED.
fn accepted(n: usize, mut run: impl FnMut() -> bool) -> usize {
    (0..n).filter(|_| run()).count()
}

struct Row {
    protocol: &'static str,
    scenario: &'static str,
    honest: bool, // true: must be accepted, so every rejection is a false rejection
    accepted: usize,
}

// The four scenarios every proof gets. make(true) builds a fresh TRUE statement and
// proves it; make(false) builds a FALSE one and runs the same honest prover on it
// (a cheater with no trapdoor). check(statement, proof, ctx) is the verifier.
fn scenarios<S, P>(
    protocol: &'static str,
    n: usize,
    make: impl Fn(bool) -> (S, P),
    check: impl Fn(&S, &P, &[u8]) -> bool,
    tamper: impl Fn(P) -> P,
) -> Vec<Row> {
    let row = |scenario, honest, count| Row { protocol, scenario, honest, accepted: count };
    vec![
        row("honest", true, accepted(n, || {
            let (s, p) = make(true);
            check(&s, &p, CTX)
        })),
        row("false statement", false, accepted(n, || {
            let (s, p) = make(false);
            check(&s, &p, CTX)
        })),
        row("replayed to another ctx", false, accepted(n, || {
            let (s, p) = make(true);
            check(&s, &p, OTHER_CTX)
        })),
        row("tampered response", false, accepted(n, || {
            let (s, p) = make(true);
            check(&s, &tamper(p), CTX)
        })),
    ]
}

#[test]
#[ignore = "slow: run with --release --ignored"]
fn false_approval_and_rejection_rates() {
    let pp = PublicParams::setup();
    let n = runs();
    let mut rows = Vec::new();

    // IDEq: c0 and c1 carry the same identity.
    rows.extend(scenarios(
        "IDEq",
        n,
        |truth| {
            let id = random_id();
            let (o0, o1) = (opening(id), opening(if truth { id } else { random_id() }));
            let (c0, c1) = (commit(&pp, &o0), commit(&pp, &o1));
            ((c0, c1), IdEqProof::prove(&pp, &c0, &c1, &o0, &o1, CTX))
        },
        |(c0, c1), p, ctx| p.verify(&pp, c0, c1, ctx),
        |p| IdEqProof { z_val: p.z_val + Scalar::ONE, ..p },
    ));

    // VVer: c holds the public value v'. A false claim is off by one.
    rows.extend(scenarios(
        "VVer",
        n,
        |truth| {
            let o = opening(random_id());
            let c = commit(&pp, &o);
            let claimed = if truth { o.val } else { o.val + Scalar::ONE };
            ((c, claimed), VVerProof::prove(&pp, &c, claimed, &o, CTX))
        },
        |(c, claimed), p, ctx| p.verify(&pp, c, *claimed, ctx),
        |p| VVerProof { z_iden: p.z_iden + Scalar::ONE, ..p },
    ));

    // VEq: c0 and c1 hold the same hidden value (different identities).
    rows.extend(scenarios(
        "VEq",
        n,
        |truth| {
            let o0 = opening(random_id());
            let val = if truth { o0.val } else { o0.val + Scalar::ONE };
            let o1 = Opening { val, ..opening(random_id()) };
            let (c0, c1) = (commit(&pp, &o0), commit(&pp, &o1));
            ((c0, c1), VEqProof::prove(&pp, &c0, &c1, &o0, &o1, CTX))
        },
        |(c0, c1), p, ctx| p.verify(&pp, c0, c1, ctx),
        |mut p| {
            p.0.z[0] += Scalar::ONE;
            p
        },
    ));

    // FullEq: c1 is a re-randomisation of c0. A false one changes the value.
    rows.extend(scenarios(
        "FullEq",
        n,
        |truth| {
            let o0 = opening(random_id());
            let val = if truth { o0.val } else { o0.val + Scalar::ONE };
            let o1 = Opening { val, blinding: random_blinding(), ..o0 };
            let (c0, c1) = (commit(&pp, &o0), commit(&pp, &o1));
            ((c0, c1), FullEqProof::prove(&pp, &c0, &c1, &o0, &o1, CTX))
        },
        |(c0, c1), p, ctx| p.verify(&pp, c0, c1, ctx),
        |mut p| {
            p.0.z[0] += Scalar::ONE;
            p
        },
    ));

    // TxVer: c_tx has c_ref's identity AND holds the declared value. A false
    // statement breaks one clause, picked at random.
    rows.extend(scenarios(
        "TxVer",
        n,
        |truth| {
            let o_ref = Opening { val: Scalar::ZERO, ..opening(random_id()) };
            let mut o_tx = opening(o_ref.id);
            let mut declared = o_tx.val;
            if !truth {
                let coin_flip = OsRng.next_u32().is_multiple_of(2);
                if coin_flip {
                    o_tx.id = random_id();
                } else {
                    declared += Scalar::ONE;
                }
            }
            let (c_ref, c_tx) = (commit(&pp, &o_ref), commit(&pp, &o_tx));
            let p = TxVerProof::prove(&pp, &c_ref, &c_tx, declared, &o_ref, &o_tx, CTX);
            ((c_ref, c_tx, declared), p)
        },
        |(c_ref, c_tx, declared), p, ctx| p.verify(&pp, c_ref, c_tx, *declared, ctx),
        |p| TxVerProof { z_iden: p.z_iden + Scalar::ONE, ..p },
    ));

    // MIDEq: all 5 commitments carry one identity. A false set hides one impostor
    // at a random position.
    rows.extend(scenarios(
        "MIDEq (n=5)",
        n,
        |truth| {
            let id = random_id();
            let mut os: Vec<Opening> = (0..5).map(|_| opening(id)).collect();
            if !truth {
                os[(OsRng.next_u32() % 5) as usize].id = random_id();
            }
            let cs: Vec<Commitment> = os.iter().map(|o| commit(&pp, o)).collect();
            let p = MIDEqProof::prove(&pp, &cs, &os, CTX);
            (cs, p)
        },
        |cs, p, ctx| p.verify(&pp, cs, ctx),
        |mut p| {
            p.0.z[0] += Scalar::ONE;
            p
        },
    ));

    // BatchVer: 8 IDEq proofs checked at once. Slot 8 is refilled every run -- with a
    // valid proof, or with a proof of a false statement -- so every run is a new batch.
    let item = |truth: bool| {
        let id = random_id();
        let (o0, o1) = (opening(id), opening(if truth { id } else { random_id() }));
        let (c0, c1) = (commit(&pp, &o0), commit(&pp, &o1));
        BatchItem { c0, c1, ctx: CTX, proof: IdEqProof::prove(&pp, &c0, &c1, &o0, &o1, CTX) }
    };
    let mut batch: Vec<BatchItem> = (0..8).map(|_| item(true)).collect();
    for (scenario, truth) in [("honest batch", true), ("one false proof in 8", false)] {
        let count = accepted(n, || {
            batch[7] = item(truth);
            batch_verify(&pp, &batch)
        });
        rows.push(Row { protocol: "BatchVer (m=8)", scenario, honest: truth, accepted: count });
    }

    println!("\nFAR / FRR over {n} fresh runs per scenario\n");
    println!("{:<15} {:<24} {:>15}   errors", "protocol", "scenario", "accepted");
    let mut errors = 0;
    for r in &rows {
        let (wrong, kind) = if r.honest {
            (n - r.accepted, "false rejections")
        } else {
            (r.accepted, "false approvals")
        };
        println!("{:<15} {:<24} {:>7} / {:<6}   {wrong} {kind}", r.protocol, r.scenario, r.accepted, n);
        errors += wrong;
    }
    println!("\n0 errors in {n} runs => that rate is below 3/{n} = {:.3} % (95 % confidence)", 300.0 / n as f64);
    assert_eq!(errors, 0, "a verifier decided wrongly -- that is a bug, not a rate");
}
