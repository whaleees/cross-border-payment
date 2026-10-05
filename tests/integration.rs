// The IBC side of the shuffle integration (integration-fix/).
// Every claim the integration document makes about IBC has a test here.
// The `limitation_*` tests PASS on purpose: each shows something IBC does not
// check, which the document must then state as an assumption.

use curve25519_dalek::Scalar;

use ibc::commitment::{Commitment, Opening, commit, random_blinding, rerand};
use ibc::ctx::RoundCtx;
use ibc::fulleq::FullEqProof;
use ibc::ideq::IdEqProof;
use ibc::mideq::MIDEqProof;
use ibc::params::{PublicParams, hash_identity, value_to_scalar};
use ibc::txver::TxVerProof;
use ibc::veq::VEqProof;
use ibc::vver::VVerProof;

const ROUND_A: [u8; 32] = [0xA; 32];
const ROUND_B: [u8; 32] = [0xB; 32];
const VALUE: u8 = 0;
const AGE: u8 = 1;

fn ctx(stage: u8, vector: u8, slot: u32) -> [u8; RoundCtx::LEN] {
    RoundCtx { round_id: ROUND_A, stage, vector, slot, prev: [0; 32] }.to_bytes()
}

fn alice() -> Scalar {
    hash_identity(b"alice")
}

// c_ref: alice's registration commitment (signed by the KYC issuer in the real system).
fn registration(pp: &PublicParams) -> (Commitment, Opening) {
    let o = Opening { id: alice(), val: Scalar::ZERO, blinding: random_blinding() };
    (commit(pp, &o), o)
}

// A two-basis commitment v*g + r*h with g = g_val, h = g_ran: an IBC opening with id = 0.
fn two_basis(v: Scalar) -> Opening {
    Opening { id: Scalar::ZERO, val: v, blinding: random_blinding() }
}

// alice's commitments to these numbers (amounts or ages).
fn alices(pp: &PublicParams, xs: &[u64]) -> (Vec<Commitment>, Vec<Opening>) {
    let os: Vec<Opening> = xs
        .iter()
        .map(|x| Opening { id: alice(), val: value_to_scalar(*x), blinding: random_blinding() })
        .collect();
    (os.iter().map(|o| commit(pp, o)).collect(), os)
}

// Re-randomise every slot, as the mixer does, and keep the new openings (Lemma 1).
fn rerand_all(pp: &PublicParams, cs: &[Commitment], os: &[Opening]) -> (Vec<Commitment>, Vec<Opening>) {
    let rhos: Vec<Scalar> = cs.iter().map(|_| random_blinding()).collect();
    let outs = cs.iter().zip(&rhos).map(|(c, rho)| rerand(pp, c, rho)).collect();
    let oos = os.iter().zip(&rhos).map(|(o, rho)| o.rerand(rho)).collect();
    (outs, oos)
}

// Lemma 5: the verifier adds the public commitments...
fn sum(cs: &[Commitment]) -> Commitment {
    cs.iter().copied().reduce(|a, b| a + b).expect("at least one commitment")
}

// ...and the prover adds the openings.
fn sum_opening(os: &[Opening]) -> Opening {
    Opening {
        id: os.iter().map(|o| o.id).sum(),
        val: os.iter().map(|o| o.val).sum(),
        blinding: os.iter().map(|o| o.blinding).sum(),
    }
}

// Stage 0: one Π.MIDEq over (c_ref, c_1..c_N).
fn stage0(
    pp: &PublicParams,
    reference: (&Commitment, &Opening),
    cs: &[Commitment],
    os: &[Opening],
    vector: u8,
) -> bool {
    let mut all_c = vec![*reference.0];
    all_c.extend_from_slice(cs);
    let mut all_o = vec![*reference.1];
    all_o.extend_from_slice(os);
    let x = ctx(0, vector, 0);
    MIDEqProof::prove(pp, &all_c, &all_o, &x).verify(pp, &all_c, &x)
}

// Stage 3: c_ST = ST*g_val + r_s*g_ran and one Π.VEq(c_sum, c_ST).
// Returns the verdict and the hidden total that Stage 4's range proof would check.
fn stage3(pp: &PublicParams, outs: &[Commitment], oos: &[Opening]) -> (bool, Scalar) {
    let o_sum = sum_opening(oos);
    let o_st = two_basis(o_sum.val);
    let c_st = commit(pp, &o_st);
    let x = ctx(3, VALUE, 0);
    let proof = VEqProof::prove(pp, &sum(outs), &c_st, &o_sum, &o_st, &x);
    (proof.verify(pp, &sum(outs), &c_st, &x), o_st.val)
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

// ---- Step 03: the round ctx --------------------------------------------------

#[test]
fn proof_does_not_move_between_rounds_stages_vectors_or_slots() {
    let pp = PublicParams::setup();
    let (c_ref, o_ref) = registration(&pp);
    let o_new = Opening { id: alice(), val: Scalar::ZERO, blinding: random_blinding() };
    let c_new = commit(&pp, &o_new);
    let here = RoundCtx { round_id: ROUND_A, stage: 2, vector: VALUE, slot: 5, prev: [0; 32] };

    let proof = TxVerProof::prove(&pp, &c_ref, &c_new, Scalar::ZERO, &o_ref, &o_new, &here.to_bytes());
    assert!(proof.verify(&pp, &c_ref, &c_new, Scalar::ZERO, &here.to_bytes()));

    // Same statement, any other ctx: rejected.
    for other in [
        RoundCtx { round_id: ROUND_B, ..here },
        RoundCtx { stage: 3, ..here },
        RoundCtx { vector: AGE, ..here },
        RoundCtx { slot: 4, ..here },
        RoundCtx { prev: [1; 32], ..here },
    ] {
        assert!(!proof.verify(&pp, &c_ref, &c_new, Scalar::ZERO, &other.to_bytes()));
    }
}

// ---- Step 04: the bridge (Lemma 4) and the hidden sum (Lemma 5) ---------------

#[test]
fn lemma4_bridge_same_value_verifies() {
    let pp = PublicParams::setup();
    let o_age = Opening { id: alice(), val: value_to_scalar(14), blinding: random_blinding() };
    let c_age = commit(&pp, &o_age);
    let o_tilde = two_basis(o_age.val);
    let c_tilde = commit(&pp, &o_tilde);
    let x = ctx(2, AGE, 5);

    // Witness (id - 0, r - r~): exactly Π.VEq's (id0 - id1, r0 - r1).
    let proof = VEqProof::prove(&pp, &c_age, &c_tilde, &o_age, &o_tilde, &x);
    assert!(proof.verify(&pp, &c_age, &c_tilde, &x));
}

#[test]
fn lemma4_bridge_wrong_value_fails() {
    let pp = PublicParams::setup();
    let o_age = Opening { id: alice(), val: value_to_scalar(3), blinding: random_blinding() };
    let c_age = commit(&pp, &o_age);
    let o_tilde = two_basis(value_to_scalar(14)); // claims an older age
    let c_tilde = commit(&pp, &o_tilde);
    let x = ctx(2, AGE, 5);

    let proof = VEqProof::prove(&pp, &c_age, &c_tilde, &o_age, &o_tilde, &x);
    assert!(!proof.verify(&pp, &c_age, &c_tilde, &x));
}

#[test]
fn lemma4_veq_alone_does_not_make_c_tilde_two_basis() {
    // c~ with a g_iden term still passes: Π.VEq lets the g_iden exponent be anything.
    // "c~ is two-basis" therefore comes from the gate's own extractor, not from Π.VEq.
    let pp = PublicParams::setup();
    let o_age = Opening { id: alice(), val: value_to_scalar(14), blinding: random_blinding() };
    let c_age = commit(&pp, &o_age);
    let o_tilde = Opening { id: Scalar::from(5u64), ..two_basis(o_age.val) };
    let c_tilde = commit(&pp, &o_tilde);
    let x = ctx(2, AGE, 5);

    let proof = VEqProof::prove(&pp, &c_age, &c_tilde, &o_age, &o_tilde, &x);
    assert!(proof.verify(&pp, &c_age, &c_tilde, &x));
}

#[test]
fn lemma5_sum_commits_to_n_times_id() {
    let pp = PublicParams::setup();
    let (cs, os) = alices(&pp, &[100, 250, 75, 300, 40]);
    let (outs, oos) = rerand_all(&pp, &cs, &os);

    let want = Opening {
        id: Scalar::from(5u64) * alice(),
        val: value_to_scalar(765),
        blinding: oos.iter().map(|o| o.blinding).sum(),
    };
    assert_eq!(sum(&outs), commit(&pp, &want));
}

#[test]
fn hidden_sum_verifies() {
    let pp = PublicParams::setup();
    let (cs, os) = alices(&pp, &[100, 250, 75, 300, 40]);
    let (outs, oos) = rerand_all(&pp, &cs, &os);
    let (ok, total) = stage3(&pp, &outs, &oos);
    assert!(ok);
    assert_eq!(total, value_to_scalar(765));
}

#[test]
fn hidden_sum_wrong_total_fails() {
    let pp = PublicParams::setup();
    let (cs, os) = alices(&pp, &[100, 250, 75, 300, 40]);
    let (outs, oos) = rerand_all(&pp, &cs, &os);
    let o_sum = sum_opening(&oos);
    let o_st = two_basis(o_sum.val - Scalar::ONE); // one less than the real total
    let c_st = commit(&pp, &o_st);
    let x = ctx(3, VALUE, 0);

    let proof = VEqProof::prove(&pp, &sum(&outs), &c_st, &o_sum, &o_st, &x);
    assert!(!proof.verify(&pp, &sum(&outs), &c_st, &x));
}

// ---- Step 05: the zeroed slot ----------------------------------------------------

#[test]
fn txver_zero_binds_c_new() {
    let pp = PublicParams::setup();
    let (c_ref, o_ref) = registration(&pp);
    let o_new = Opening { id: alice(), val: Scalar::ZERO, blinding: random_blinding() };
    let c_new = commit(&pp, &o_new);
    let x = ctx(2, VALUE, 5);

    let proof = TxVerProof::prove(&pp, &c_ref, &c_new, Scalar::ZERO, &o_ref, &o_new, &x);
    assert!(proof.verify(&pp, &c_ref, &c_new, Scalar::ZERO, &x));
}

#[test]
fn txver_zero_rejects_a_nonzero_c_new() {
    let pp = PublicParams::setup();
    let (c_ref, o_ref) = registration(&pp);
    let o_new = Opening { id: alice(), val: -value_to_scalar(500), blinding: random_blinding() };
    let c_new = commit(&pp, &o_new);
    let x = ctx(2, VALUE, 5);

    let proof = TxVerProof::prove(&pp, &c_ref, &c_new, Scalar::ZERO, &o_ref, &o_new, &x);
    assert!(!proof.verify(&pp, &c_ref, &c_new, Scalar::ZERO, &x));
}

#[test]
fn txver_zero_rejects_a_foreign_c_new() {
    let pp = PublicParams::setup();
    let (c_ref, o_ref) = registration(&pp);
    let o_new = Opening { id: hash_identity(b"bob"), val: Scalar::ZERO, blinding: random_blinding() };
    let c_new = commit(&pp, &o_new);
    let x = ctx(2, VALUE, 5);

    let proof = TxVerProof::prove(&pp, &c_ref, &c_new, Scalar::ZERO, &o_ref, &o_new, &x);
    assert!(!proof.verify(&pp, &c_ref, &c_new, Scalar::ZERO, &x));
}

// slot + c_delta, where c_delta carries `delta_id`. Does Π.TxVer(c_ref, ., 0) accept?
fn zero_slot_with(delta_id: Scalar) -> bool {
    let pp = PublicParams::setup();
    let (c_ref, o_ref) = registration(&pp);
    let o_slot = Opening { id: alice(), val: value_to_scalar(300), blinding: random_blinding() };
    let o_delta = Opening { id: delta_id, val: -o_slot.val, blinding: random_blinding() };
    let zeroed = commit(&pp, &o_slot) + commit(&pp, &o_delta);
    // The only opening the prover has: the two added together.
    let o_zeroed = Opening {
        id: o_slot.id + o_delta.id,
        val: o_slot.val + o_delta.val,
        blinding: o_slot.blinding + o_delta.blinding,
    };
    let x = ctx(2, VALUE, 5);
    TxVerProof::prove(&pp, &c_ref, &zeroed, Scalar::ZERO, &o_ref, &o_zeroed, &x)
        .verify(&pp, &c_ref, &zeroed, Scalar::ZERO, &x)
}

#[test]
fn delta_with_identity_doubles_it() {
    // c_delta = Com(id, -v_k): slot + c_delta = Com(2*id, 0), not alice's.
    assert!(!zero_slot_with(alice()));
}

#[test]
fn delta_without_identity_zeroes_the_slot() {
    // c_delta = Com(0, -v_k): slot + c_delta = Com(id, 0), alice's, value 0.
    assert!(zero_slot_with(Scalar::ZERO));
}

#[test]
fn stage3_does_not_check_identity() {
    // A c_new that belongs to bob still passes the hidden sum: Π.VEq ignores g_iden.
    // c_new's identity is bound by Π.TxVer in Stage 2 or not at all.
    let pp = PublicParams::setup();
    let (cs, os) = alices(&pp, &[100, 250, 75, 300]);
    let (mut outs, mut oos) = rerand_all(&pp, &cs, &os);
    let o_new = Opening { id: hash_identity(b"bob"), val: Scalar::ZERO, blinding: random_blinding() };
    outs.push(commit(&pp, &o_new));
    oos.push(o_new);
    assert!(stage3(&pp, &outs, &oos).0);
}

// ---- Step 06: the IBC side of a whole round, and its limits -----------------------

#[test]
fn round_b_ibc_side_accepts() {
    let pp = PublicParams::setup();
    let (c_ref, o_ref) = registration(&pp);
    // The last slot holds the expired transaction once the second shuffle is done.
    let (cs, os) = alices(&pp, &[100, 250, 75, 300, 9_000]);
    let (ages, oages) = alices(&pp, &[1, 2, 3, 4, 14]);
    let last = cs.len() - 1;
    let n = cs.len() as u32;

    // Stage 0: both vectors bound to c_ref.
    assert!(stage0(&pp, (&c_ref, &o_ref), &cs, &os, VALUE));
    assert!(stage0(&pp, (&c_ref, &o_ref), &ages, &oages, AGE));

    // Stages 1-2 re-randomise. The permutations are Azka's; IBC only needs ReRand.
    let (outs, oos) = rerand_all(&pp, &cs, &os);
    let (age_outs, oage_outs) = rerand_all(&pp, &ages, &oages);

    // Stage 2: bridge the target's age to a two-basis copy for the age gate.
    let o_tilde = two_basis(oage_outs[last].val);
    let c_tilde = commit(&pp, &o_tilde);
    let x_br = ctx(2, AGE, n);
    let p_br = VEqProof::prove(&pp, &age_outs[last], &c_tilde, &oage_outs[last], &o_tilde, &x_br);
    assert!(p_br.verify(&pp, &age_outs[last], &c_tilde, &x_br));

    // Stage 2: c_new = Com(id, 0), bound to c_ref by Π.TxVer with v' = 0.
    let o_new = Opening { id: alice(), val: Scalar::ZERO, blinding: random_blinding() };
    let c_new = commit(&pp, &o_new);
    let x_tx = ctx(2, VALUE, n);
    let p_tx = TxVerProof::prove(&pp, &c_ref, &c_new, Scalar::ZERO, &o_ref, &o_new, &x_tx);
    assert!(p_tx.verify(&pp, &c_ref, &c_new, Scalar::ZERO, &x_tx));

    // Stage 3: the sum with the last slot replaced by c_new.
    let mut summed = outs[..last].to_vec();
    summed.push(c_new);
    let mut summed_o = oos[..last].to_vec();
    summed_o.push(o_new);
    let (ok, total) = stage3(&pp, &summed, &summed_o);
    assert!(ok);
    assert_eq!(total, value_to_scalar(725)); // the expired 9 000 is not counted
}

#[test]
fn limitation_an_omitted_transaction_goes_unnoticed() {
    // alice really made [100, 250, 75, 9 000, 40]; she submits the set without 9 000.
    let pp = PublicParams::setup();
    let (c_ref, o_ref) = registration(&pp);
    let (cs, os) = alices(&pp, &[100, 250, 75, 40]);
    assert!(stage0(&pp, (&c_ref, &o_ref), &cs, &os, VALUE));
    let (outs, oos) = rerand_all(&pp, &cs, &os);
    let (ok, total) = stage3(&pp, &outs, &oos);
    assert!(ok);
    assert_eq!(total, value_to_scalar(465)); // the 9 000 never entered the sum
}

#[test]
fn limitation_ages_can_be_paired_with_the_wrong_transaction() {
    // Honest: the 9 000 payment is 1 month old, the 100 payment 14 months old.
    // alice commits the ages swapped, so the 9 000 payment looks expired.
    let pp = PublicParams::setup();
    let (c_ref, o_ref) = registration(&pp);
    let (cs, os) = alices(&pp, &[9_000, 100]);
    let (ages, oages) = alices(&pp, &[14, 1]); // swapped
    assert!(stage0(&pp, (&c_ref, &o_ref), &cs, &os, VALUE));
    assert!(stage0(&pp, (&c_ref, &o_ref), &ages, &oages, AGE));
}

#[test]
fn limitation_a_negative_value_lowers_the_hidden_sum() {
    // Scalars are mod p, so -7 000 (that is, p - 7 000) is a valid amount. The
    // total lands inside [0, B] although the real volume is 8 000.
    let pp = PublicParams::setup();
    let (c_ref, o_ref) = registration(&pp);
    let (mut cs, mut os) = alices(&pp, &[5_000, 3_000]);
    let o_neg = Opening { id: alice(), val: -value_to_scalar(7_000), blinding: random_blinding() };
    cs.push(commit(&pp, &o_neg));
    os.push(o_neg);

    assert!(stage0(&pp, (&c_ref, &o_ref), &cs, &os, VALUE));
    let (outs, oos) = rerand_all(&pp, &cs, &os);
    let (ok, total) = stage3(&pp, &outs, &oos);
    assert!(ok);
    assert_eq!(total, value_to_scalar(1_000));
}
