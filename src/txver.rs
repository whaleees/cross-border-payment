use curve25519_dalek::{
    RistrettoPoint, Scalar,
    traits::{Identity, VartimeMultiscalarMul},
};
use rand_core::OsRng;

use crate::commitment::{Commitment, Opening};
use crate::params::PublicParams;
use crate::transcript::Challenge;

pub struct TxVerProof {
    pub t1: RistrettoPoint,
    pub t2: RistrettoPoint,
    pub z_val: Scalar,  
    pub z_1: Scalar,    
    pub z_iden: Scalar, 
    pub z_2: Scalar,    
}

const DS: &[u8] = b"IBC/v1/TxVer";
const DS_DELTA: &[u8] = b"IBC/v1/TxVer-delta";

fn challenge(
    pp: &PublicParams,
    c_ref: &Commitment,
    c_tx: &Commitment,
    v_pub: &Scalar,
    ctx: &[u8],
    t1: &RistrettoPoint,
    t2: &RistrettoPoint,
) -> Scalar {
    Challenge::new(DS, pp)
        .point(b"c_ref", &c_ref.0)
        .point(b"c_tx", &c_tx.0)
        .scalar(b"v", v_pub)
        .bytes(b"ctx", ctx)
        .point(b"t1", t1)
        .point(b"t2", t2)
        .finish()
}

fn merge_weight(
    pp: &PublicParams,
    c_ref: &Commitment,
    c_tx: &Commitment,
    v_pub: &Scalar,
    ctx: &[u8],
    proof: &TxVerProof,
) -> Scalar {
    Challenge::new(DS_DELTA, pp)
        .point(b"c_ref", &c_ref.0)
        .point(b"c_tx", &c_tx.0)
        .scalar(b"v", v_pub)
        .bytes(b"ctx", ctx)
        .point(b"t1", &proof.t1)
        .point(b"t2", &proof.t2)
        .scalar(b"z_val", &proof.z_val)
        .scalar(b"z_1", &proof.z_1)
        .scalar(b"z_iden", &proof.z_iden)
        .scalar(b"z_2", &proof.z_2)
        .finish()
}

impl TxVerProof {
    pub fn prove(
        pp: &PublicParams,
        c_ref: &Commitment,
        c_tx: &Commitment,
        v_pub: Scalar,
        o_ref: &Opening,
        o_tx: &Opening,
        ctx: &[u8],
    ) -> Self {
        let alpha_val = Scalar::random(&mut OsRng);
        let alpha_1 = Scalar::random(&mut OsRng);
        let alpha_iden = Scalar::random(&mut OsRng);
        let alpha_2 = Scalar::random(&mut OsRng);

        let t1 = alpha_val * pp.g_val + alpha_1 * pp.g_ran; // clause 1 bases
        let t2 = alpha_iden * pp.g_iden + alpha_2 * pp.g_ran; // clause 2 bases

        let beta = challenge(pp, c_ref, c_tx, &v_pub, ctx, &t1, &t2);

        let z_val = beta * (o_ref.val - o_tx.val) + alpha_val;
        let z_1 = beta * (o_ref.blinding - o_tx.blinding) + alpha_1;
        let z_iden = beta * o_tx.id + alpha_iden;
        let z_2 = beta * o_tx.blinding + alpha_2;

        TxVerProof { t1, t2, z_val, z_1, z_iden, z_2 }
    }

    pub fn verify(
        &self,
        pp: &PublicParams,
        c_ref: &Commitment,
        c_tx: &Commitment,
        v_pub: Scalar,
        ctx: &[u8],
    ) -> bool {
        let beta = challenge(pp, c_ref, c_tx, &v_pub, ctx, &self.t1, &self.t2);
        let delta = merge_weight(pp, c_ref, c_tx, &v_pub, ctx, self);

        let scalars = [
            delta * self.z_iden,               // g_iden
            self.z_val + delta * beta * v_pub, // g_val
            self.z_1 + delta * self.z_2,       // g_ran
            -Scalar::ONE,                      // t1
            -delta,                            // t2
            -beta,                             // c_ref
            beta - delta * beta,               // c_tx
        ];
        let points = [pp.g_iden, pp.g_val, pp.g_ran, self.t1, self.t2, c_ref.0, c_tx.0];

        RistrettoPoint::vartime_multiscalar_mul(scalars, points) == RistrettoPoint::identity()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commitment::{commit, random_blinding};
    use crate::params::{hash_identity, value_to_scalar};

    // A registered user and a transaction commitment that (honestly) shares the
    // identity and declares value `v`.
    fn valid_tx(
        v: u64,
    ) -> (PublicParams, Commitment, Commitment, Opening, Opening, Scalar) {
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let v_pub = value_to_scalar(v);
        let o_ref = Opening { id, val: value_to_scalar(0), blinding: random_blinding() }; // registration
        let o_tx = Opening { id, val: v_pub, blinding: random_blinding() };
        let c_ref = commit(&pp, &o_ref);
        let c_tx = commit(&pp, &o_tx);
        (pp, c_ref, c_tx, o_ref, o_tx, v_pub)
    }

    #[test]
    fn valid_transaction_verifies() {
        let (pp, c_ref, c_tx, o_ref, o_tx, v) = valid_tx(1_500);
        let proof = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, b"tx-001");
        assert!(proof.verify(&pp, &c_ref, &c_tx, v, b"tx-001"));
    }

    #[test]
    fn wrong_identity_fails() {
        // c_tx belongs to a different user than c_ref -> clause 1 breaks.
        let pp = PublicParams::setup();
        let v = value_to_scalar(1_500);
        let o_ref = Opening { id: hash_identity(b"alice"), val: value_to_scalar(0), blinding: random_blinding() };
        let o_tx = Opening { id: hash_identity(b"mallory"), val: v, blinding: random_blinding() };
        let c_ref = commit(&pp, &o_ref);
        let c_tx = commit(&pp, &o_tx);

        let proof = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, b"tx-001");
        assert!(!proof.verify(&pp, &c_ref, &c_tx, v, b"tx-001"));
    }

    #[test]
    fn wrong_value_fails() {
        // c_tx holds a different value than declared -> clause 2 breaks.
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let o_ref = Opening { id, val: value_to_scalar(0), blinding: random_blinding() };
        let o_tx = Opening { id, val: value_to_scalar(999), blinding: random_blinding() };
        let c_ref = commit(&pp, &o_ref);
        let c_tx = commit(&pp, &o_tx);

        let declared = value_to_scalar(1_500);
        let proof = TxVerProof::prove(&pp, &c_ref, &c_tx, declared, &o_ref, &o_tx, b"tx-001");
        assert!(!proof.verify(&pp, &c_ref, &c_tx, declared, b"tx-001"));
    }

    #[test]
    fn declared_value_mismatch_fails() {
        // Honest proof for v, but verifier checks against v+1.
        let (pp, c_ref, c_tx, o_ref, o_tx, v) = valid_tx(1_500);
        let proof = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, b"tx-001");
        assert!(!proof.verify(&pp, &c_ref, &c_tx, value_to_scalar(1_501), b"tx-001"));
    }

    #[test]
    fn proof_is_bound_to_the_context() {
        let (pp, c_ref, c_tx, o_ref, o_tx, v) = valid_tx(1_500);
        let proof = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, b"tx-001");
        assert!(!proof.verify(&pp, &c_ref, &c_tx, v, b"tx-002"));
    }

    #[test]
    fn clauses_cannot_be_mixed() {
        // Splice clause 2 from proof B into proof A. The two proofs have different
        // challenges, and B's clause-2 answers fit B's challenge, not A's, so the
        // spliced proof fails. On its own this only catches a challenge that
        // ignores BOTH t1 and t2; challenge_depends_on_every_input and
        // value_clause_cannot_be_forged_backwards cover the rest.
        let (pp, c_ref, c_tx, o_ref, o_tx, v) = valid_tx(1_500);
        let a = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, b"tx-001");
        let b = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, b"tx-001");

        let spliced = TxVerProof {
            t1: a.t1,
            z_val: a.z_val,
            z_1: a.z_1,
            t2: b.t2, // from B
            z_iden: b.z_iden, // from B
            z_2: b.z_2, // from B
        };
        assert!(!spliced.verify(&pp, &c_ref, &c_tx, v, b"tx-001"));
    }

    #[test]
    fn challenge_depends_on_every_input() {
        // Spec step 3: beta = H(ds, pp, c_ref, c_tx, v', ctx, t1, t2). Change any
        // one input and beta must change -- otherwise that input is not bound.
        let (pp, c_ref, c_tx, o_ref, o_tx, v) = valid_tx(1_500);
        let p = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, b"tx-001");
        let beta = challenge(&pp, &c_ref, &c_tx, &v, b"tx-001", &p.t1, &p.t2);

        let x = RistrettoPoint::random(&mut OsRng); // any other point
        let other = Commitment(x);
        assert_ne!(beta, challenge(&pp, &other, &c_tx, &v, b"tx-001", &p.t1, &p.t2));
        assert_ne!(beta, challenge(&pp, &c_ref, &other, &v, b"tx-001", &p.t1, &p.t2));
        assert_ne!(beta, challenge(&pp, &c_ref, &c_tx, &(v + Scalar::ONE), b"tx-001", &p.t1, &p.t2));
        assert_ne!(beta, challenge(&pp, &c_ref, &c_tx, &v, b"tx-002", &p.t1, &p.t2));
        assert_ne!(beta, challenge(&pp, &c_ref, &c_tx, &v, b"tx-001", &x, &p.t2));
        assert_ne!(beta, challenge(&pp, &c_ref, &c_tx, &v, b"tx-001", &p.t1, &x));
    }

    #[test]
    fn value_clause_cannot_be_forged_backwards() {
        // c_tx really holds 999 but 1_500 is declared, so the prover has no witness
        // for clause 2. The simulator trick: pick z_iden, z_2 first, then solve
        // t2 = z_iden*g_iden + z_2*g_ran - beta*U2. That needs beta before t2, so
        // the forger hashes a placeholder t2 -- which only works if beta ignores t2.
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let o_ref = Opening { id, val: value_to_scalar(0), blinding: random_blinding() };
        let o_tx = Opening { id, val: value_to_scalar(999), blinding: random_blinding() };
        let c_ref = commit(&pp, &o_ref);
        let c_tx = commit(&pp, &o_tx);
        let declared = value_to_scalar(1_500);

        // Clause 1 honestly: the identity really does match.
        let alpha_val = random_blinding();
        let alpha_1 = random_blinding();
        let t1 = alpha_val * pp.g_val + alpha_1 * pp.g_ran;
        let beta = challenge(&pp, &c_ref, &c_tx, &declared, b"tx-001", &t1, &RistrettoPoint::identity());
        let z_val = beta * (o_ref.val - o_tx.val) + alpha_val;
        let z_1 = beta * (o_ref.blinding - o_tx.blinding) + alpha_1;

        // Clause 2 backwards, with no witness.
        let z_iden = random_blinding();
        let z_2 = random_blinding();
        let u2 = c_tx.0 - declared * pp.g_val;
        let t2 = z_iden * pp.g_iden + z_2 * pp.g_ran - beta * u2;

        let forged = TxVerProof { t1, t2, z_val, z_1, z_iden, z_2 };
        assert!(!forged.verify(&pp, &c_ref, &c_tx, declared, b"tx-001"));
    }

    #[test]
    fn masks_do_not_leak_the_identity() {
        // alpha_1 and alpha_2 must be separate draws. With one shared mask,
        // z_1 - z_2 = beta*(r_ref - 2*r_tx) would be public, and with v_ref = 0
        // anyone could compute the user's fingerprint id*g_iden from public data:
        //   2*c_tx + (r_ref - 2*r_tx)*g_ran - 2*v'*g_val - c_ref = id*g_iden
        let (pp, c_ref, c_tx, o_ref, o_tx, v) = valid_tx(1_500);
        let p = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, b"tx-001");
        let beta = challenge(&pp, &c_ref, &c_tx, &v, b"tx-001", &p.t1, &p.t2);

        let two = Scalar::from(2u64);
        let d = (p.z_1 - p.z_2) * beta.invert();
        let fingerprint = two * c_tx.0 + d * pp.g_ran - two * v * pp.g_val - c_ref.0;
        assert_ne!(fingerprint, hash_identity(b"alice") * pp.g_iden);
    }

    #[test]
    fn plain_sum_forgery_is_rejected() {
        // Why verify needs delta. In E1 + E2 the c_tx terms cancel, leaving
        //   z_val*g_val + (z_1 + z_2)*g_ran + z_iden*g_iden == t1 + t2 + beta*(c_ref - v'*g_val)
        // Anyone who can open c_ref can satisfy that for ANY c_tx. Build such a
        // proof for a c_tx that belongs to someone else and holds the wrong value.
        let pp = PublicParams::setup();
        let o_ref = Opening { id: hash_identity(b"alice"), val: value_to_scalar(0), blinding: random_blinding() };
        let o_other = Opening { id: hash_identity(b"mallory"), val: value_to_scalar(999), blinding: random_blinding() };
        let c_ref = commit(&pp, &o_ref);
        let c_tx = commit(&pp, &o_other);
        let declared = value_to_scalar(1_500);

        let (a_val, a_ran, a_iden) = (random_blinding(), random_blinding(), random_blinding());
        let t1 = a_val * pp.g_val + a_ran * pp.g_ran;
        let t2 = a_iden * pp.g_iden;
        let beta = challenge(&pp, &c_ref, &c_tx, &declared, b"tx-001", &t1, &t2);
        let forged = TxVerProof {
            t1,
            t2,
            z_val: beta * (o_ref.val - declared) + a_val,
            z_1: beta * o_ref.blinding + a_ran,
            z_iden: beta * o_ref.id + a_iden,
            z_2: Scalar::ZERO,
        };

        // It really does satisfy the plain sum...
        let lhs = forged.z_val * pp.g_val + (forged.z_1 + forged.z_2) * pp.g_ran + forged.z_iden * pp.g_iden;
        assert_eq!(lhs, t1 + t2 + beta * (c_ref.0 - declared * pp.g_val));
        // ...but not the weighted check.
        assert!(!forged.verify(&pp, &c_ref, &c_tx, declared, b"tx-001"));
    }

    #[test]
    fn merge_weight_depends_on_the_responses() {
        // delta must be fixed only after the whole proof is. If it ignored the z's,
        // the prover would know it before choosing them and could solve the single
        // merged equation with the openings it holds, true statement or not.
        let (pp, c_ref, c_tx, o_ref, o_tx, v) = valid_tx(1_500);
        let p = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, b"tx-001");
        let delta = merge_weight(&pp, &c_ref, &c_tx, &v, b"tx-001", &p);

        let one = Scalar::ONE;
        let changed = [
            TxVerProof { z_val: p.z_val + one, ..p },
            TxVerProof { z_1: p.z_1 + one, ..p },
            TxVerProof { z_iden: p.z_iden + one, ..p },
            TxVerProof { z_2: p.z_2 + one, ..p },
        ];
        for q in &changed {
            assert_ne!(delta, merge_weight(&pp, &c_ref, &c_tx, &v, b"tx-001", q));
        }
    }

    #[test]
    fn proof_size_is_192_bytes() {
        // 2 points + 4 scalars = 192 bytes.
        let (pp, c_ref, c_tx, o_ref, o_tx, v) = valid_tx(1_500);
        let p = TxVerProof::prove(&pp, &c_ref, &c_tx, v, &o_ref, &o_tx, b"tx-001");
        let size = p.t1.compress().to_bytes().len()
            + p.t2.compress().to_bytes().len()
            + p.z_val.as_bytes().len()
            + p.z_1.as_bytes().len()
            + p.z_iden.as_bytes().len()
            + p.z_2.as_bytes().len();
        assert_eq!(size, 192);
    }
}
