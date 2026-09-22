use curve25519_dalek::{RistrettoPoint, Scalar};
use rand_core::OsRng;

use crate::commitment::{Commitment, Opening};
use crate::params::PublicParams;
use crate::transcript::Challenge;

pub struct IdEqProof {
    pub t: RistrettoPoint,
    pub z_val: Scalar,
    pub z_ran: Scalar,
}

pub fn commit(pp: &PublicParams) -> ((Scalar, Scalar), RistrettoPoint)
{
    let alpha_val = Scalar::random(&mut OsRng);
    let alpha_ran = Scalar::random(&mut OsRng);
    let t = alpha_val * pp.g_val + alpha_ran * pp.g_ran;

    ((alpha_val, alpha_ran), t)
}

pub fn respond(
    masks: (Scalar, Scalar),
    beta: Scalar,
    o0: &Opening,
    o1: &Opening,
) -> (Scalar, Scalar) {
    let (alpha_val, alpha_ran) = masks;
    let z_val = beta * (o0.val - o1.val) + alpha_val;
    let z_ran = beta * (o0.blinding - o1.blinding) + alpha_ran;

    (z_val, z_ran)
}

pub fn check(
    pp: &PublicParams,
    c0: &Commitment,
    c1: &Commitment,
    proof: &IdEqProof,
    beta: Scalar,
) -> bool {
    let lhs = proof.z_val * pp.g_val + proof.z_ran * pp.g_ran;
    let rhs = proof.t + beta * (c0.0 - c1.0);

    lhs == rhs
}

// Fiat-Shamir challenge for Pi.IDEq: beta = H(ds, pp, c0, c1, ctx, t).
// Built here (not caller-supplied) so beta is a pure function of the public inputs.
fn challenge(
    pp: &PublicParams,
    c0: &Commitment,
    c1: &Commitment,
    ctx: &[u8],
    t: &RistrettoPoint,
) -> Scalar {
    Challenge::new(b"IBC/v1/IDEq", pp)
        .point(b"c0", &c0.0)
        .point(b"c1", &c1.0)
        .bytes(b"ctx", ctx)
        .point(b"t", t)
        .finish()
}

impl IdEqProof {
    // Non-interactive prove
    pub fn prove(
        pp: &PublicParams,
        c0: &Commitment,
        c1: &Commitment,
        o0: &Opening,
        o1: &Opening,
        ctx: &[u8],
    ) -> Self {
        let (masks, t) = commit(pp);
        let beta = challenge(pp, c0, c1, ctx, &t);
        let (z_val, z_ran) = respond(masks, beta, o0, o1);
        IdEqProof { t, z_val, z_ran }
    }

    // Non-interactive verify
    pub fn verify(
        &self,
        pp: &PublicParams,
        c0: &Commitment,
        c1: &Commitment,
        ctx: &[u8],
    ) -> bool {
        let beta = challenge(pp, c0, c1, ctx, &self.t);
        check(pp, c0, c1, self, beta)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commitment::random_blinding;
    use crate::params::{hash_identity, value_to_scalar};

    // The commitment module's `commit` clashes with this module's `commit`
    // (Round 1 of the proof), so wrap it under a distinct name for the tests.
    fn commit_to(pp: &PublicParams, o: &Opening) -> Commitment {
        crate::commitment::commit(pp, o)
    }

    #[test]
    fn same_identity_verifies() {
        // Same id, but DIFFERENT value and DIFFERENT blinding in each commitment,
        // so only a correct witness computation can pass.
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let o0 = Opening { id, val: value_to_scalar(100), blinding: random_blinding() };
        let o1 = Opening { id, val: value_to_scalar(250), blinding: random_blinding() };
        let c0 = commit_to(&pp, &o0);
        let c1 = commit_to(&pp, &o1);

        let (masks, t) = commit(&pp);
        let beta = Scalar::random(&mut OsRng);
        let (z_val, z_ran) = respond(masks, beta, &o0, &o1);
        let proof = IdEqProof { t, z_val, z_ran };

        assert!(check(&pp, &c0, &c1, &proof, beta));
    }

    #[test]
    fn different_identities_fail() {
        let pp = PublicParams::setup();
        let o0 = Opening { id: hash_identity(b"alice"), val: value_to_scalar(100), blinding: random_blinding() };
        let o1 = Opening { id: hash_identity(b"bob"),   val: value_to_scalar(250), blinding: random_blinding() };
        let c0 = commit_to(&pp, &o0);
        let c1 = commit_to(&pp, &o1);

        let (masks, t) = commit(&pp);
        let beta = Scalar::random(&mut OsRng);
        let (z_val, z_ran) = respond(masks, beta, &o0, &o1);
        let proof = IdEqProof { t, z_val, z_ran };

        // The leftover (id0 - id1)*g_iden term makes the check fail.
        assert!(!check(&pp, &c0, &c1, &proof, beta));
    }

    #[test]
    fn identical_commitments_verify() {
        // c0 == c1: every difference is zero, a valid (trivial) case.
        let pp = PublicParams::setup();
        let o = Opening { id: hash_identity(b"alice"), val: value_to_scalar(100), blinding: random_blinding() };
        let c0 = commit_to(&pp, &o);
        let c1 = c0;

        let (masks, t) = commit(&pp);
        let beta = Scalar::random(&mut OsRng);
        let (z_val, z_ran) = respond(masks, beta, &o, &o);
        let proof = IdEqProof { t, z_val, z_ran };

        assert!(check(&pp, &c0, &c1, &proof, beta));
    }

    #[test]
    fn wrong_challenge_fails() {
        // A proof answered for beta does not satisfy a different challenge.
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let o0 = Opening { id, val: value_to_scalar(100), blinding: random_blinding() };
        let o1 = Opening { id, val: value_to_scalar(250), blinding: random_blinding() };
        let c0 = commit_to(&pp, &o0);
        let c1 = commit_to(&pp, &o1);

        let (masks, t) = commit(&pp);
        let beta = Scalar::random(&mut OsRng);
        let (z_val, z_ran) = respond(masks, beta, &o0, &o1);
        let proof = IdEqProof { t, z_val, z_ran };

        let other_beta = Scalar::random(&mut OsRng);
        assert!(!check(&pp, &c0, &c1, &proof, other_beta));
    }

    #[test]
    fn wrong_witness_fails() {
        // Same-identity commitments (an honest proof would pass), but respond()
        // is given the wrong opening, so the masked witness is wrong.
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let o0 = Opening { id, val: value_to_scalar(100), blinding: random_blinding() };
        let o1 = Opening { id, val: value_to_scalar(250), blinding: random_blinding() };
        let c0 = commit_to(&pp, &o0);
        let c1 = commit_to(&pp, &o1);

        let (masks, t) = commit(&pp);
        let beta = Scalar::random(&mut OsRng);
        // Wrong second opening: a different value than the one committed in c1.
        let o1_bad = Opening { val: value_to_scalar(999), ..o1 };
        let (z_val, z_ran) = respond(masks, beta, &o0, &o1_bad);
        let proof = IdEqProof { t, z_val, z_ran };

        assert!(!check(&pp, &c0, &c1, &proof, beta));
    }

    #[test]
    fn extractor_recovers_the_witness() {
        // Special soundness: two accepting transcripts sharing t but with
        // different challenges reveal the witness (dv, dr) = (v0-v1, r0-r1).
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let o0 = Opening { id, val: value_to_scalar(100), blinding: random_blinding() };
        let o1 = Opening { id, val: value_to_scalar(250), blinding: random_blinding() };

        let (masks, _t) = commit(&pp);
        let beta1 = Scalar::random(&mut OsRng);
        let beta2 = Scalar::random(&mut OsRng);
        let (zv1, zr1) = respond(masks, beta1, &o0, &o1);
        let (zv2, zr2) = respond(masks, beta2, &o0, &o1);

        // Each coordinate is a 1-D Schnorr extractor: divide the z-difference
        // by the challenge difference (invert() needs prime order + beta1 != beta2).
        let inv = (beta1 - beta2).invert();
        let dv = (zv1 - zv2) * inv;
        let dr = (zr1 - zr2) * inv;

        assert_eq!(dv, o0.val - o1.val);
        assert_eq!(dr, o0.blinding - o1.blinding);
    }

    fn same_id_pair() -> (PublicParams, Opening, Opening, Commitment, Commitment) {
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let o0 = Opening { id, val: value_to_scalar(100), blinding: random_blinding() };
        let o1 = Opening { id, val: value_to_scalar(250), blinding: random_blinding() };
        let c0 = commit_to(&pp, &o0);
        let c1 = commit_to(&pp, &o1);
        (pp, o0, o1, c0, c1)
    }

    #[test]
    fn ni_proof_verifies() {
        let (pp, o0, o1, c0, c1) = same_id_pair();
        let proof = IdEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert!(proof.verify(&pp, &c0, &c1, b"tx-001"));
    }

    #[test]
    fn proof_is_bound_to_the_statement() {
        // Prove for (c0, c1). Verify against (c0, c2). Must fail.
        let (pp, o0, o1, c0, c1) = same_id_pair();
        let proof = IdEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");

        let o2 = Opening { id: hash_identity(b"bob"), val: value_to_scalar(250), blinding: random_blinding() };
        let c2 = commit_to(&pp, &o2);
        assert!(!proof.verify(&pp, &c0, &c2, b"tx-001"));
    }

    #[test]
    fn proof_is_bound_to_the_context() {
        // Prove with ctx = tx-001. Verify with ctx = tx-002. Must fail.
        let (pp, o0, o1, c0, c1) = same_id_pair();
        let proof = IdEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert!(!proof.verify(&pp, &c0, &c1, b"tx-002"));
    }

    #[test]
    fn fiat_shamir_equals_the_interactive_protocol() {
        // A non-interactive proof, fed to the interactive check() at the
        // recomputed beta, must pass: the two forms are the same protocol.
        let (pp, o0, o1, c0, c1) = same_id_pair();
        let proof = IdEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        let beta = challenge(&pp, &c0, &c1, b"tx-001", &proof.t);
        assert!(check(&pp, &c0, &c1, &proof, beta));
    }

    #[test]
    fn two_proofs_for_the_same_statement_differ() {
        // Fresh masks each time, so proofs are randomised.
        let (pp, o0, o1, c0, c1) = same_id_pair();
        let p1 = IdEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        let p2 = IdEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert_ne!(p1.t, p2.t);
    }
}