use curve25519_dalek::{RistrettoPoint, Scalar};
use rand_core::OsRng;

use crate::{
    commitment::{Commitment, Opening},
    params::PublicParams,
};

pub struct VVerProof {
    pub t: RistrettoPoint,
    pub z_iden: Scalar,
    pub z_ran: Scalar,
}

pub fn commit(pp: &PublicParams) -> ((Scalar, Scalar), RistrettoPoint)
{
    let alpha_iden = Scalar::random(&mut OsRng);
    let alpha_ran = Scalar::random(&mut OsRng);
    let t = alpha_iden * pp.g_iden + alpha_ran * pp.g_ran;
    
    ((alpha_iden, alpha_ran), t)
}

pub fn respond(masks: (Scalar, Scalar), beta: Scalar, o: &Opening)
    -> (Scalar, Scalar)
{
    let (alpha_iden, alpha_ran) = masks;

    (beta * o.id + alpha_iden, beta * o.blinding + alpha_ran)
}

pub fn check(
    pp: &PublicParams,
    c: &Commitment,
    v_pub: Scalar,
    proof: &VVerProof,
    beta: Scalar,
) -> bool {
    let u = c.0 - v_pub * pp.g_val;
    let lhs = proof.z_iden * pp.g_iden + proof.z_ran * pp.g_ran;
    let rhs = proof.t + beta * u;
    
    lhs == rhs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commitment::random_blinding;
    use crate::params::{hash_identity, value_to_scalar};

    // Distinct name for the commitment constructor, to avoid clashing with
    // this module's `commit` (Round 1 of the proof).
    fn commit_to(pp: &PublicParams, o: &Opening) -> Commitment {
        crate::commitment::commit(pp, o)
    }

    #[test]
    fn correct_value_verifies() {
        let pp = PublicParams::setup();
        let v = value_to_scalar(1_500);
        let o = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let c = commit_to(&pp, &o);

        let (masks, t) = commit(&pp);
        let beta = Scalar::random(&mut OsRng);
        let (z_iden, z_ran) = respond(masks, beta, &o);
        let proof = VVerProof { t, z_iden, z_ran };

        assert!(check(&pp, &c, v, &proof, beta));
    }

    #[test]
    fn wrong_public_value_fails() {
        // The distinguishing test: prove honestly for v', check against v'+1.
        let pp = PublicParams::setup();
        let v = value_to_scalar(1_500);
        let o = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let c = commit_to(&pp, &o);

        let (masks, t) = commit(&pp);
        let beta = Scalar::random(&mut OsRng);
        let (z_iden, z_ran) = respond(masks, beta, &o);
        let proof = VVerProof { t, z_iden, z_ran };

        assert!(!check(&pp, &c, value_to_scalar(1_501), &proof, beta));
    }

    #[test]
    fn wrong_identity_witness_fails() {
        let pp = PublicParams::setup();
        let v = value_to_scalar(1_500);
        let o = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let c = commit_to(&pp, &o);

        let (masks, t) = commit(&pp);
        let beta = Scalar::random(&mut OsRng);
        // Respond with the wrong identity.
        let o_bad = Opening { id: hash_identity(b"mallory"), ..o };
        let (z_iden, z_ran) = respond(masks, beta, &o_bad);
        let proof = VVerProof { t, z_iden, z_ran };

        assert!(!check(&pp, &c, v, &proof, beta));
    }

    #[test]
    fn wrong_blinding_witness_fails() {
        let pp = PublicParams::setup();
        let v = value_to_scalar(1_500);
        let o = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let c = commit_to(&pp, &o);

        let (masks, t) = commit(&pp);
        let beta = Scalar::random(&mut OsRng);
        // Respond with the wrong blinding.
        let o_bad = Opening { blinding: random_blinding(), ..o };
        let (z_iden, z_ran) = respond(masks, beta, &o_bad);
        let proof = VVerProof { t, z_iden, z_ran };

        assert!(!check(&pp, &c, v, &proof, beta));
    }

    #[test]
    fn zero_value_verifies() {
        // v = 0 is a legitimate edge case: the stripped element is just c.
        let pp = PublicParams::setup();
        let v = value_to_scalar(0);
        let o = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let c = commit_to(&pp, &o);

        let (masks, t) = commit(&pp);
        let beta = Scalar::random(&mut OsRng);
        let (z_iden, z_ran) = respond(masks, beta, &o);
        let proof = VVerProof { t, z_iden, z_ran };

        assert!(check(&pp, &c, v, &proof, beta));
    }

    #[test]
    fn proof_against_different_commitment_fails() {
        let pp = PublicParams::setup();
        let v = value_to_scalar(1_500);
        let o = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let c = commit_to(&pp, &o);

        let (masks, t) = commit(&pp);
        let beta = Scalar::random(&mut OsRng);
        let (z_iden, z_ran) = respond(masks, beta, &o);
        let proof = VVerProof { t, z_iden, z_ran };

        // A different commitment (same value, different id and blinding).
        let other = Opening { id: hash_identity(b"bob"), val: v, blinding: random_blinding() };
        let c_other = commit_to(&pp, &other);

        assert!(!check(&pp, &c_other, v, &proof, beta));
    }

    #[test]
    fn extractor_recovers_the_witness() {
        // Special soundness: two accepting transcripts sharing t but with
        // different challenges reveal the witness (id, r).
        let pp = PublicParams::setup();
        let v = value_to_scalar(1_500);
        let o = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };

        let (masks, _t) = commit(&pp);
        let beta1 = Scalar::random(&mut OsRng);
        let beta2 = Scalar::random(&mut OsRng);
        let (zi1, zr1) = respond(masks, beta1, &o);
        let (zi2, zr2) = respond(masks, beta2, &o);

        let inv = (beta1 - beta2).invert();
        let id_star = (zi1 - zi2) * inv;
        let r_star = (zr1 - zr2) * inv;

        assert_eq!(id_star, o.id);
        assert_eq!(r_star, o.blinding);
    }
}