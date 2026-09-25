use crate::commitment::{Commitment, Opening};
use crate::params::PublicParams;
use crate::sigma::{self, SigmaProof};
use crate::transcript::Challenge;

pub struct FullEqProof(pub SigmaProof);

const DS: &[u8] = b"IBC/v1/FullEq";

fn bind<'a>(
    c0: &'a Commitment,
    c1: &'a Commitment,
    ctx: &'a [u8],
) -> impl FnOnce(Challenge) -> Challenge + 'a {
    move |ch| ch.point(b"c0", &c0.0).point(b"c1", &c1.0).bytes(b"ctx", ctx)
}

impl FullEqProof {
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
            &[pp.g_ran],                     // ONE base
            &[o0.blinding - o1.blinding],    // ONE witness
            bind(c0, c1, ctx),
        );
        FullEqProof(sp)
    }

    pub fn verify(
        &self,
        pp: &PublicParams,
        c0: &Commitment,
        c1: &Commitment,
        ctx: &[u8],
    ) -> bool {
        sigma::verify(pp, DS, &[pp.g_ran], &(c0.0 - c1.0), &self.0, bind(c0, c1, ctx))
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        self.0.to_bytes()
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        SigmaProof::from_bytes(bytes, 1).map(FullEqProof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commitment::{commit, random_blinding};
    use crate::params::{hash_identity, value_to_scalar};

    // Build c0 and a genuine re-randomisation c1 = c0 + rho*g_ran.
    fn rerandomised_pair() -> (PublicParams, Opening, Opening, Commitment, Commitment) {
        let pp = PublicParams::setup();
        let o0 = Opening {
            id: hash_identity(b"alice"),
            val: value_to_scalar(1_500),
            blinding: random_blinding(),
        };
        let rho = random_blinding();
        let o1 = Opening { blinding: o0.blinding + rho, ..o0 };
        let c0 = commit(&pp, &o0);
        let c1 = commit(&pp, &o1); // = c0 + rho*g_ran
        (pp, o0, o1, c0, c1)
    }

    #[test]
    fn rerandomisation_verifies() {
        let (pp, o0, o1, c0, c1) = rerandomised_pair();
        let proof = FullEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert!(proof.verify(&pp, &c0, &c1, b"tx-001"));
    }

    #[test]
    fn different_identity_fails() {
        // A leftover (id0-id1)*g_iden term cannot be absorbed by g_ran alone.
        let pp = PublicParams::setup();
        let o0 = Opening { id: hash_identity(b"alice"), val: value_to_scalar(1_500), blinding: random_blinding() };
        let o1 = Opening { id: hash_identity(b"bob"),   val: value_to_scalar(1_500), blinding: random_blinding() };
        let c0 = commit(&pp, &o0);
        let c1 = commit(&pp, &o1);

        let proof = FullEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert!(!proof.verify(&pp, &c0, &c1, b"tx-001"));
    }

    #[test]
    fn different_value_fails() {
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let o0 = Opening { id, val: value_to_scalar(1_500), blinding: random_blinding() };
        let o1 = Opening { id, val: value_to_scalar(1_501), blinding: random_blinding() };
        let c0 = commit(&pp, &o0);
        let c1 = commit(&pp, &o1);

        let proof = FullEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert!(!proof.verify(&pp, &c0, &c1, b"tx-001"));
    }

    #[test]
    fn proof_is_bound_to_the_context() {
        let (pp, o0, o1, c0, c1) = rerandomised_pair();
        let proof = FullEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert!(!proof.verify(&pp, &c0, &c1, b"tx-002"));
    }

    #[test]
    fn proof_does_not_transfer_to_a_shifted_pair() {
        // Add the same commitment x to both sides. c0 - c1 (the target U) is
        // unchanged and (c0 + x, c1 + x) is still a genuine re-randomisation, so
        // the check equation alone would still pass. Only binding c0 and c1
        // themselves into beta rejects it.
        let (pp, o0, o1, c0, c1) = rerandomised_pair();
        let proof = FullEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001");
        assert!(proof.verify(&pp, &c0, &c1, b"tx-001"));

        let ox = Opening { id: hash_identity(b"carol"), val: value_to_scalar(7), blinding: random_blinding() };
        let x = commit(&pp, &ox);
        assert!(!proof.verify(&pp, &(c0 + x), &(c1 + x), b"tx-001"));
    }

    #[test]
    fn proof_size_is_64_bytes() {
        // Measured on the real encoding, then decoded and verified.
        let (pp, o0, o1, c0, c1) = rerandomised_pair();
        let bytes = FullEqProof::prove(&pp, &c0, &c1, &o0, &o1, b"tx-001").to_bytes();
        assert_eq!(bytes.len(), 64);
        let decoded = FullEqProof::from_bytes(&bytes).expect("valid encoding");
        assert!(decoded.verify(&pp, &c0, &c1, b"tx-001"));
    }
}
