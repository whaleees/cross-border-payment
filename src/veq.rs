use crate::commitment::{Commitment, Opening};
use crate::params::PublicParams;
use crate::sigma::{self, SigmaProof};
use crate::transcript::Challenge;

pub struct VEqProof(pub SigmaProof);

const DS: &[u8] = b"IBC/v1/VEq";

// Single source of truth for how Π.VEq binds its statement into the challenge.
fn bind<'a>(
    c0: &'a Commitment,
    c1: &'a Commitment,
    ctx: &'a [u8],
) -> impl FnOnce(Challenge) -> Challenge + 'a {
    move |ch| ch.point(b"c0", &c0.0).point(b"c1", &c1.0).bytes(b"ctx", ctx)
}

impl VEqProof {
    pub fn prove(
        pp: &PublicParams,
        c0: &Commitment,
        c1: &Commitment,
        o0: &Opening,
        o1: &Opening,
        ctx: &[u8],
    ) -> Self {
        let sp = sigma::prove(
            pp,
            DS,
            &[pp.g_iden, pp.g_ran],
            &[o0.id - o1.id, o0.blinding - o1.blinding],
            bind(c0, c1, ctx),
        );
        VEqProof(sp)
    }

    pub fn verify(
        &self,
        pp: &PublicParams,
        c0: &Commitment,
        c1: &Commitment,
        ctx: &[u8],
    ) -> bool {
        sigma::verify(
            pp,
            DS,
            &[pp.g_iden, pp.g_ran],
            &(c0.0 - c1.0),
            &self.0,
            bind(c0, c1, ctx),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commitment::{commit, random_blinding};
    use crate::params::{hash_identity, value_to_scalar};

    #[test]
    fn same_value_verifies() {
        // The normal IBC case: same identity (id0 - id1 = 0), same value,
        // different blindings. The different-identity case is
        // same_value_across_two_users.
        let pp = PublicParams::setup();
        let v = value_to_scalar(500);
        let o0 = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let o1 = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let c0 = commit(&pp, &o0);
        let c1 = commit(&pp, &o1);

        let proof = VEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert!(proof.verify(&pp, &c0, &c1, b"tx-001"));
    }

    #[test]
    fn different_values_fail() {
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let o0 = Opening { id, val: value_to_scalar(500), blinding: random_blinding() };
        let o1 = Opening { id, val: value_to_scalar(501), blinding: random_blinding() };
        let c0 = commit(&pp, &o0);
        let c1 = commit(&pp, &o1);

        let proof = VEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert!(!proof.verify(&pp, &c0, &c1, b"tx-001"));
    }

    #[test]
    fn same_value_across_two_users() {
        // Different identities, same value -> still verifies. This is the
        // sender/receiver consistency case Π.VVer cannot express.
        let pp = PublicParams::setup();
        let v = value_to_scalar(500);
        let o0 = Opening { id: hash_identity(b"sender"),   val: v, blinding: random_blinding() };
        let o1 = Opening { id: hash_identity(b"receiver"), val: v, blinding: random_blinding() };
        let c0 = commit(&pp, &o0);
        let c1 = commit(&pp, &o1);

        let proof = VEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert!(proof.verify(&pp, &c0, &c1, b"tx-001"));
    }

    #[test]
    fn proof_is_bound_to_the_context() {
        let pp = PublicParams::setup();
        let v = value_to_scalar(500);
        let o0 = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let o1 = Opening { id: hash_identity(b"bob"),   val: v, blinding: random_blinding() };
        let c0 = commit(&pp, &o0);
        let c1 = commit(&pp, &o1);

        let proof = VEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert!(!proof.verify(&pp, &c0, &c1, b"tx-002"));
    }

    #[test]
    fn proof_is_bound_to_the_statement() {
        let pp = PublicParams::setup();
        let v = value_to_scalar(500);
        let o0 = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let o1 = Opening { id: hash_identity(b"bob"),   val: v, blinding: random_blinding() };
        let c0 = commit(&pp, &o0);
        let c1 = commit(&pp, &o1);

        let proof = VEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");

        // A different second commitment (different value) -> must fail. The
        // leftover g_val term alone makes this fail, whatever beta is, so the
        // binding itself is tested by proof_does_not_transfer_to_a_shifted_pair.
        let o2 = Opening { id: hash_identity(b"bob"), val: value_to_scalar(999), blinding: random_blinding() };
        let c2 = commit(&pp, &o2);
        assert!(!proof.verify(&pp, &c0, &c2, b"tx-001"));
    }

    #[test]
    fn proof_does_not_transfer_to_a_shifted_pair() {
        // Add the same commitment x to both sides. c0 - c1 (the target U) is
        // unchanged and the values are still equal, so the check equation alone
        // would still pass. Only binding c0 and c1 themselves into beta rejects it.
        let pp = PublicParams::setup();
        let v = value_to_scalar(500);
        let o0 = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let o1 = Opening { id: hash_identity(b"bob"),   val: v, blinding: random_blinding() };
        let c0 = commit(&pp, &o0);
        let c1 = commit(&pp, &o1);

        let proof = VEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert!(proof.verify(&pp, &c0, &c1, b"tx-001"));

        let ox = Opening { id: hash_identity(b"carol"), val: value_to_scalar(7), blinding: random_blinding() };
        let x = commit(&pp, &ox);
        assert!(!proof.verify(&pp, &(c0 + x), &(c1 + x), b"tx-001"));
    }

    #[test]
    fn two_proofs_for_the_same_statement_differ() {
        let pp = PublicParams::setup();
        let v = value_to_scalar(500);
        let o0 = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let o1 = Opening { id: hash_identity(b"bob"),   val: v, blinding: random_blinding() };
        let c0 = commit(&pp, &o0);
        let c1 = commit(&pp, &o1);

        let p1 = VEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        let p2 = VEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert_ne!(p1.0.t, p2.0.t);
    }
}
