use curve25519_dalek::{RistrettoPoint, Scalar, traits::Identity};
use rand_core::OsRng;

use crate::params::PublicParams;
use crate::transcript::Challenge;

#[derive(Clone, Debug)]
pub struct SigmaProof {
    pub t: RistrettoPoint,
    pub z: Vec<Scalar>,
}

fn linear_combination(scalars: &[Scalar], points: &[RistrettoPoint]) -> RistrettoPoint {
    scalars
        .iter()
        .zip(points)
        .fold(RistrettoPoint::identity(), |acc, (s, p)| acc + *s * *p)
}

pub fn prove(
    pp: &PublicParams,
    domain: &'static [u8],
    bases: &[RistrettoPoint],
    witness: &[Scalar],
    bind: impl FnOnce(Challenge) -> Challenge,
) -> SigmaProof {
    assert_eq!(
        bases.len(),
        witness.len(),
        "sigma::prove: bases and witness must have equal length"
    );

    // Round 1: one fresh mask per base, then t.
    let alphas: Vec<Scalar> = (0..bases.len())
        .map(|_| Scalar::random(&mut OsRng))
        .collect();
    let t = linear_combination(&alphas, bases);

    // Challenge: statement first (via bind), then t. Pure function of public data.
    let beta = bind(Challenge::new(domain, pp)).point(b"t", &t).finish();

    // Round 3: mask each witness coordinate with the challenge.
    let z = witness
        .iter()
        .zip(&alphas)
        .map(|(w, a)| beta * w + a)
        .collect();

    SigmaProof { t, z }
}

pub fn verify(
    pp: &PublicParams,
    domain: &'static [u8],
    bases: &[RistrettoPoint],
    u: &RistrettoPoint,
    proof: &SigmaProof,
    bind: impl FnOnce(Challenge) -> Challenge,
) -> bool {
    if proof.z.len() != bases.len() {
        return false;
    }

    let beta = bind(Challenge::new(domain, pp))
        .point(b"t", &proof.t)
        .finish();

    let lhs = linear_combination(&proof.z, bases);
    let rhs = proof.t + beta * u;
    lhs == rhs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commitment::{Commitment, Opening, commit, random_blinding};
    use crate::ideq::IdEqProof;
    use crate::params::{PublicParams, hash_identity, value_to_scalar};
    use crate::vver::VVerProof;

    fn two_base_stmt(pp: &PublicParams, w0: Scalar, w1: Scalar) -> RistrettoPoint {
        w0 * pp.g_iden + w1 * pp.g_ran
    }

    #[test]
    fn honest_two_base_verifies() {
        let pp = PublicParams::setup();
        let bases = [pp.g_iden, pp.g_ran];
        let w = [value_to_scalar(7), value_to_scalar(9)];
        let u = two_base_stmt(&pp, w[0], w[1]);

        let proof = prove(&pp, b"test/2base", &bases, &w, |ch| ch.point(b"u", &u));
        assert!(verify(&pp, b"test/2base", &bases, &u, &proof, |ch| ch.point(b"u", &u)));
    }

    #[test]
    fn honest_one_base_verifies() {
        let pp = PublicParams::setup();
        let bases = [pp.g_ran];
        let w = [random_blinding()];
        let u = w[0] * pp.g_ran;

        let proof = prove(&pp, b"test/1base", &bases, &w, |ch| ch.point(b"u", &u));
        assert!(verify(&pp, b"test/1base", &bases, &u, &proof, |ch| ch.point(b"u", &u)));
    }

    #[test]
    fn wrong_witness_fails() {
        let pp = PublicParams::setup();
        let bases = [pp.g_iden, pp.g_ran];
        let w = [value_to_scalar(7), value_to_scalar(9)];
        let u = two_base_stmt(&pp, w[0], w[1]);

        // Prove for a witness that does not open u.
        let bad = [value_to_scalar(7), value_to_scalar(10)];
        let proof = prove(&pp, b"test/2base", &bases, &bad, |ch| ch.point(b"u", &u));
        assert!(!verify(&pp, b"test/2base", &bases, &u, &proof, |ch| ch.point(b"u", &u)));
    }

    #[test]
    fn wrong_statement_binding_fails() {
        // Same proof, but the verifier binds a different statement into beta.
        let pp = PublicParams::setup();
        let bases = [pp.g_iden, pp.g_ran];
        let w = [value_to_scalar(7), value_to_scalar(9)];
        let u = two_base_stmt(&pp, w[0], w[1]);

        let proof = prove(&pp, b"test/2base", &bases, &w, |ch| ch.bytes(b"ctx", b"A"));
        assert!(!verify(&pp, b"test/2base", &bases, &u, &proof, |ch| ch.bytes(b"ctx", b"B")));
    }

    #[test]
    fn length_mismatch_is_rejected() {
        let pp = PublicParams::setup();
        let bases = [pp.g_iden, pp.g_ran];
        let w = [value_to_scalar(7), value_to_scalar(9)];
        let u = two_base_stmt(&pp, w[0], w[1]);
        let mut proof = prove(&pp, b"test/2base", &bases, &w, |ch| ch.point(b"u", &u));

        proof.z.pop(); // now one response for two bases
        assert!(!verify(&pp, b"test/2base", &bases, &u, &proof, |ch| ch.point(b"u", &u)));
    }

    #[test]
    fn simulator_produces_an_accepting_transcript() {
        // Zero-knowledge, concretely (interactive form, where beta is free):
        // build an accepting (t, beta, z) WITHOUT a witness by working backwards
        // from the check. Pick z and beta at random, then set t = Lz - beta*U.
        let pp = PublicParams::setup();
        let bases = [pp.g_iden, pp.g_ran];
        let u = two_base_stmt(&pp, value_to_scalar(7), value_to_scalar(9));

        let z = [random_blinding(), random_blinding()];
        let beta = random_blinding();
        let t = linear_combination(&z, &bases) - beta * u;

        // The verification equation holds for this simulated transcript.
        assert_eq!(linear_combination(&z, &bases), t + beta * u);
    }

    #[test]
    fn extractor_recovers_the_witness() {
        // Special soundness: two accepting transcripts sharing t, different beta,
        // reveal the witness. We reach into the interactive core by reusing masks.
        let pp = PublicParams::setup();
        let bases = [pp.g_iden, pp.g_ran];
        let w = [value_to_scalar(7), value_to_scalar(9)];

        let alphas = [random_blinding(), random_blinding()];
        let t = linear_combination(&alphas, &bases);
        let beta1 = random_blinding();
        let beta2 = random_blinding();
        let z1: Vec<Scalar> = w.iter().zip(&alphas).map(|(x, a)| beta1 * x + a).collect();
        let z2: Vec<Scalar> = w.iter().zip(&alphas).map(|(x, a)| beta2 * x + a).collect();

        let inv = (beta1 - beta2).invert();
        for i in 0..2 {
            let extracted = (z1[i] - z2[i]) * inv;
            assert_eq!(extracted, w[i]);
        }
        let _ = t;
    }

    // ---- equivalence: the engine IS Pi.IDEq and Pi.VVer -------------------

    fn same_id_pair() -> (PublicParams, Opening, Opening, Commitment, Commitment) {
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let o0 = Opening { id, val: value_to_scalar(100), blinding: random_blinding() };
        let o1 = Opening { id, val: value_to_scalar(250), blinding: random_blinding() };
        let c0 = commit(&pp, &o0);
        let c1 = commit(&pp, &o1);
        (pp, o0, o1, c0, c1)
    }

    #[test]
    fn engine_proof_is_accepted_by_the_real_ideq_verifier() {
        // The engine, given Pi.IDEq's (U, bases, witness, domain, bind), produces
        // a proof that the hand-written IdEqProof::verify accepts unchanged.
        let (pp, o0, o1, c0, c1) = same_id_pair();
        let ctx: &[u8] = b"tx-001";

        let sp = prove(
            &pp,
            b"IBC/v1/IDEq",
            &[pp.g_val, pp.g_ran],
            &[o0.val - o1.val, o0.blinding - o1.blinding],
            |ch| ch.point(b"c0", &c0.0).point(b"c1", &c1.0).bytes(b"ctx", ctx),
        );

        let idproof = IdEqProof { t: sp.t, z_val: sp.z[0], z_ran: sp.z[1] };
        assert!(idproof.verify(&pp, &c0, &c1, ctx));
    }

    #[test]
    fn real_ideq_proof_is_accepted_by_the_engine() {
        // And the reverse: a genuine IdEqProof verifies under the engine.
        let (pp, o0, o1, c0, c1) = same_id_pair();
        let ctx: &[u8] = b"tx-001";

        let real = IdEqProof::prove(&pp, &c0, &c1, &o0, &o1, ctx);
        let sp = SigmaProof { t: real.t, z: vec![real.z_val, real.z_ran] };

        assert!(verify(
            &pp,
            b"IBC/v1/IDEq",
            &[pp.g_val, pp.g_ran],
            &(c0.0 - c1.0),
            &sp,
            |ch| ch.point(b"c0", &c0.0).point(b"c1", &c1.0).bytes(b"ctx", ctx),
        ));
    }

    #[test]
    fn engine_proof_is_accepted_by_the_real_vver_verifier() {
        let pp = PublicParams::setup();
        let v = value_to_scalar(1_500);
        let o = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let c = commit(&pp, &o);
        let ctx: &[u8] = b"tx-001";

        // Pi.VVer: U = c - v'*g_val, bases {g_iden, g_ran}, witness (id, r).
        let u = c.0 - v * pp.g_val;
        let sp = prove(
            &pp,
            b"IBC/v1/VVer",
            &[pp.g_iden, pp.g_ran],
            &[o.id, o.blinding],
            |ch| ch.point(b"c", &c.0).scalar(b"v", &v).bytes(b"ctx", ctx),
        );
        let _ = u;

        let vproof = VVerProof { t: sp.t, z_iden: sp.z[0], z_ran: sp.z[1] };
        assert!(vproof.verify(&pp, &c, v, ctx));
    }

    #[test]
    fn real_vver_proof_is_accepted_by_the_engine() {
        let pp = PublicParams::setup();
        let v = value_to_scalar(1_500);
        let o = Opening { id: hash_identity(b"alice"), val: v, blinding: random_blinding() };
        let c = commit(&pp, &o);
        let ctx: &[u8] = b"tx-001";

        let real = VVerProof::prove(&pp, &c, v, &o, ctx);
        let sp = SigmaProof { t: real.t, z: vec![real.z_iden, real.z_ran] };

        assert!(verify(
            &pp,
            b"IBC/v1/VVer",
            &[pp.g_iden, pp.g_ran],
            &(c.0 - v * pp.g_val),
            &sp,
            |ch| ch.point(b"c", &c.0).scalar(b"v", &v).bytes(b"ctx", ctx),
        ));
    }
}
