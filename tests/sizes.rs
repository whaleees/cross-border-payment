use curve25519_dalek::{RistrettoPoint, Scalar};

use ibc::commitment::{Commitment, Opening, commit, random_blinding};
use ibc::fulleq::FullEqProof;
use ibc::ideq::IdEqProof;
use ibc::mideq::MIDEqProof;
use ibc::params::{PublicParams, hash_identity, value_to_scalar};
use ibc::sigma::SigmaProof;
use ibc::txver::TxVerProof;
use ibc::veq::VEqProof;
use ibc::vver::VVerProof;

const CTX: &[u8] = b"tx-000001";

// Bytes of a real proof, field by field: 32 per group element, 32 per scalar.
fn point_bytes(p: &RistrettoPoint) -> usize {
    p.compress().to_bytes().len()
}
fn scalar_bytes(s: &Scalar) -> usize {
    s.as_bytes().len()
}
fn sigma_bytes(p: &SigmaProof) -> usize {
    point_bytes(&p.t) + p.z.iter().map(scalar_bytes).sum::<usize>()
}

// n of alice's commitments, each a different value and blinding.
fn same_identity(pp: &PublicParams, n: usize) -> (Vec<Commitment>, Vec<Opening>) {
    let id = hash_identity(b"alice");
    let os: Vec<Opening> = (0..n as u64)
        .map(|k| Opening { id, val: value_to_scalar(100 + k), blinding: random_blinding() })
        .collect();
    (os.iter().map(|o| commit(pp, o)).collect(), os)
}

#[test]
fn proof_sizes() {
    // The fixtures of step 03, and one proof of each kind.
    let pp = PublicParams::setup();
    let id = hash_identity(b"alice");
    let v = value_to_scalar(1_500);
    let o_ref = Opening { id, val: value_to_scalar(0), blinding: random_blinding() };
    let o_tx = Opening { id, val: v, blinding: random_blinding() };
    let (c_ref, c_tx) = (commit(&pp, &o_ref), commit(&pp, &o_tx));
    let o_bob = Opening { id: hash_identity(b"bob"), val: v, blinding: random_blinding() };
    let c_bob = commit(&pp, &o_bob);
    let o_rr = Opening { blinding: o_tx.blinding + random_blinding(), ..o_tx };
    let c_rr = commit(&pp, &o_rr);
    let (cs, os) = same_identity(&pp, 10);

    let pi = IdEqProof::prove(&pp, &c_ref, &c_tx, &o_ref, &o_tx, CTX);
    let pv = VVerProof::prove(&pp, &c_tx, v, &o_tx, CTX);
    let pe = VEqProof::prove(&pp, &c_tx, &c_bob, &o_tx, &o_bob, CTX);
    let pf = FullEqProof::prove(&pp, &c_tx, &c_rr, &o_tx, &o_rr, CTX);
    let pt = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, CTX);
    let pm = MIDEqProof::prove(&pp, &cs, &os, CTX);

    let commitment = point_bytes(&c_tx.0);
    let ideq = point_bytes(&pi.t) + scalar_bytes(&pi.z_val) + scalar_bytes(&pi.z_ran);
    let vver = point_bytes(&pv.t) + scalar_bytes(&pv.z_iden) + scalar_bytes(&pv.z_ran);
    let veq = sigma_bytes(&pe.0);
    let fulleq = sigma_bytes(&pf.0);
    let mideq = sigma_bytes(&pm.0);
    let txver = point_bytes(&pt.t1)
        + point_bytes(&pt.t2)
        + [pt.z_val, pt.z_1, pt.z_iden, pt.z_2].iter().map(scalar_bytes).sum::<usize>();

    assert_eq!(commitment, 32);
    assert_eq!(ideq, 96);
    assert_eq!(vver, 96);
    assert_eq!(veq, 96);
    assert_eq!(fulleq, 64);
    assert_eq!(mideq, 96);
    assert_eq!(txver, 192);

    // Pi.MIDEq is 96 B for ANY n -- the point of task (b). Check two very different n.
    let (cs2, os2) = same_identity(&pp, 2);
    let (cs100, os100) = same_identity(&pp, 100);
    let small = MIDEqProof::prove(&pp, &cs2, &os2, CTX);
    let big = MIDEqProof::prove(&pp, &cs100, &os100, CTX);
    assert_eq!(sigma_bytes(&small.0), 96);
    assert_eq!(sigma_bytes(&big.0), 96);

    // Run with --nocapture to copy the table into the thesis.
    println!(
        "commitment {commitment}  ideq {ideq}  vver {vver}  veq {veq}  \
         fulleq {fulleq}  mideq {mideq}  txver {txver}"
    );
}
