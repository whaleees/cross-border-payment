// The IBC side of the shuffle integration (integration-fix/).
// Every claim the integration document makes about IBC has a test here.
// The `limitation_*` tests PASS on purpose: each shows something IBC does not
// check, which the document must then state as an assumption.

use curve25519_dalek::Scalar;

use ibc::commitment::{Commitment, Opening, commit, random_blinding, rerand};
use ibc::fulleq::FullEqProof;
use ibc::ideq::IdEqProof;
use ibc::mideq::MIDEqProof;
use ibc::params::{PublicParams, hash_identity, value_to_scalar};
use ibc::txver::TxVerProof;
use ibc::veq::VEqProof;
use ibc::vver::VVerProof;

fn alice() -> Scalar {
    hash_identity(b"alice")
}

// c_ref: alice's registration commitment (signed by the KYC issuer in the real system).
fn registration(pp: &PublicParams) -> (Commitment, Opening) {
    let o = Opening { id: alice(), val: Scalar::ZERO, blinding: random_blinding() };
    (commit(pp, &o), o)
}

// ---- Step 01: ReRand and Lemma 3 ---------------------------------------------

#[test]
fn lemma3_every_proof_still_works_after_rerand() {
    let pp = PublicParams::setup();
    let (c_ref, o_ref) = registration(&pp);
    let o = Opening { id: alice(), val: value_to_scalar(250), blinding: random_blinding() };
    let c = commit(&pp, &o);
    let rho = random_blinding();
    let (c_out, o_out) = (rerand(&pp, &c, &rho), o.rerand(&rho));
    let v = o.val;
    let x = b"lemma3";

    assert!(IdEqProof::prove(&pp, &c_ref, &c_out, &o_ref, &o_out, x).verify(&pp, &c_ref, &c_out, x));
    assert!(VVerProof::prove(&pp, &c_out, v, &o_out, x).verify(&pp, &c_out, v, x));
    assert!(VEqProof::prove(&pp, &c, &c_out, &o, &o_out, x).verify(&pp, &c, &c_out, x));
    assert!(FullEqProof::prove(&pp, &c, &c_out, &o, &o_out, x).verify(&pp, &c, &c_out, x));
    assert!(TxVerProof::prove(&pp, &c_ref, &c_out, v, &o_ref, &o_out, x).verify(&pp, &c_ref, &c_out, v, x));
    let (cs, os) = ([c_ref, c_out], [o_ref, o_out]);
    assert!(MIDEqProof::prove(&pp, &cs, &os, x).verify(&pp, &cs, x));
}

#[test]
fn lemma3_needs_the_new_opening() {
    // The prover must keep r + rho. Proving with the old opening fails.
    let pp = PublicParams::setup();
    let o = Opening { id: alice(), val: value_to_scalar(250), blinding: random_blinding() };
    let c_out = rerand(&pp, &commit(&pp, &o), &random_blinding());
    let x = b"lemma3";
    assert!(!VVerProof::prove(&pp, &c_out, o.val, &o, x).verify(&pp, &c_out, o.val, x));
}
