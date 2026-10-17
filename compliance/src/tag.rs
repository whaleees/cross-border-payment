use curve25519_dalek::{
    RistrettoPoint, Scalar,
    traits::{Identity, VartimeMultiscalarMul},
};
use ibc::commitment::{Commitment, Opening, random_blinding};
use ibc::transcript::Challenge;

use crate::params::Params;

// Pi.Tag: tid and tag hold the same id, and tag carries nothing else.
//   tid = id*g_iden + s*g_ran        (clause 1)
//   tag = id*g_tag                   (clause 2)
// One mask alpha for id in both clauses, so one response z_id must satisfy both.
// Written by hand like Pi.TxVer: Kresna's sigma engine proves one equation, and
// folding the two clauses into one before t is fixed lets a tag carry an extra
// g_ran term (single_equation_shortcut_accepts_a_forged_tag).
pub struct TagProof {
    pub t1: RistrettoPoint,
    pub t2: RistrettoPoint,
    pub z_id: Scalar,
    pub z_s: Scalar,
}

const DS: &[u8] = b"compliance/v1/Tag";
const DS_DELTA: &[u8] = b"compliance/v1/Tag-delta";

// The registration tag: no blinding, so the same id always gives the same tag.
pub fn tag(params: &Params, id: &Scalar) -> RistrettoPoint {
    id * params.g_tag
}

fn challenge(
    params: &Params,
    tid: &Commitment,
    tag: &RistrettoPoint,
    ctx: &[u8],
    t1: &RistrettoPoint,
    t2: &RistrettoPoint,
) -> Scalar {
    Challenge::new(DS, &params.pp)
        .point(b"g_tag", &params.g_tag)
        .point(b"tid", &tid.0)
        .point(b"tag", tag)
        .bytes(b"ctx", ctx)
        .point(b"t1", t1)
        .point(b"t2", t2)
        .finish()
}

// Weight that merges the two clauses into one MSM. It hashes the responses too, so
// it is fixed only after the whole proof is (same reason as Pi.TxVer's delta).
fn merge_weight(params: &Params, tid: &Commitment, tag: &RistrettoPoint, ctx: &[u8], proof: &TagProof) -> Scalar {
    Challenge::new(DS_DELTA, &params.pp)
        .point(b"g_tag", &params.g_tag)
        .point(b"tid", &tid.0)
        .point(b"tag", tag)
        .bytes(b"ctx", ctx)
        .point(b"t1", &proof.t1)
        .point(b"t2", &proof.t2)
        .scalar(b"z_id", &proof.z_id)
        .scalar(b"z_s", &proof.z_s)
        .finish()
}

impl TagProof {
    pub fn prove(params: &Params, tid: &Commitment, tag: &RistrettoPoint, o_tid: &Opening, ctx: &[u8]) -> Self {
        let alpha = random_blinding(); // masks id, shared by both clauses
        let beta = random_blinding(); // masks tid's blinding

        let t1 = alpha * params.pp.g_iden + beta * params.pp.g_ran;
        let t2 = alpha * params.g_tag;

        let c = challenge(params, tid, tag, ctx, &t1, &t2);

        TagProof { t1, t2, z_id: alpha + c * o_tid.id, z_s: beta + c * o_tid.blinding }
    }

    pub fn verify(&self, params: &Params, tid: &Commitment, tag: &RistrettoPoint, ctx: &[u8]) -> bool {
        let c = challenge(params, tid, tag, ctx, &self.t1, &self.t2);
        let delta = merge_weight(params, tid, tag, ctx, self);

        // clause 1 + delta * clause 2, as one MSM:
        //   z_id*g_iden + z_s*g_ran - t1 - c*tid  +  delta*(z_id*g_tag - t2 - c*tag)  == 0
        let scalars = [self.z_id, self.z_s, -Scalar::ONE, -c, delta * self.z_id, -delta, -(delta * c)];
        let points = [params.pp.g_iden, params.pp.g_ran, self.t1, tid.0, params.g_tag, self.t2, *tag];

        RistrettoPoint::vartime_multiscalar_mul(scalars, points) == RistrettoPoint::identity()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ibc::commitment::commit;
    use ibc::params::hash_identity;
    use ibc::sigma;

    const CTX: &[u8] = b"round-1";

    // tid for this id: a commitment to (id, 0) with a fresh blinding.
    fn tid_for(params: &Params, id: Scalar) -> (Commitment, Opening) {
        let o = Opening { id, val: Scalar::ZERO, blinding: random_blinding() };
        (commit(&params.pp, &o), o)
    }

    // The textbook check: both clauses, one at a time.
    fn two_equations_hold(params: &Params, p: &TagProof, tid: &Commitment, tag: &RistrettoPoint, ctx: &[u8]) -> bool {
        let c = challenge(params, tid, tag, ctx, &p.t1, &p.t2);
        let clause1 = p.z_id * params.pp.g_iden + p.z_s * params.pp.g_ran == p.t1 + c * tid.0;
        let clause2 = p.z_id * params.g_tag == p.t2 + c * tag;
        clause1 && clause2
    }

    #[test]
    fn valid_tag_verifies() {
        let params = Params::setup();
        let id = hash_identity(b"alice");
        let (tid, o_tid) = tid_for(&params, id);
        let t = tag(&params, &id);

        let proof = TagProof::prove(&params, &tid, &t, &o_tid, CTX);
        assert!(proof.verify(&params, &tid, &t, CTX));
    }

    #[test]
    fn the_tag_depends_on_the_id_only() {
        // Two tids for alice look unrelated, but her tag is the same both times;
        // bob's is different. This is what lets the nullifier set spot a re-registration.
        let params = Params::setup();
        let (alice, bob) = (hash_identity(b"alice"), hash_identity(b"bob"));
        let (tid1, _) = tid_for(&params, alice);
        let (tid2, _) = tid_for(&params, alice);
        assert_ne!(tid1, tid2);
        assert_eq!(tag(&params, &alice), tag(&params, &alice));
        assert_ne!(tag(&params, &alice), tag(&params, &bob));
    }

    #[test]
    fn a_tag_for_another_identity_fails() {
        // tid is alice's, the tag is bob's: clause 2 has no witness with alice's id.
        let params = Params::setup();
        let alice = hash_identity(b"alice");
        let (tid, o_tid) = tid_for(&params, alice);
        let bobs_tag = tag(&params, &hash_identity(b"bob"));

        let proof = TagProof::prove(&params, &tid, &bobs_tag, &o_tid, CTX);
        assert!(!proof.verify(&params, &tid, &bobs_tag, CTX));
    }

    #[test]
    fn a_tag_with_a_blinding_term_fails() {
        // The reset attack: tag' = id*g_tag + b*g_ran is a NEW tag for the SAME
        // person, which the nullifier set would not recognise. Clause 2 has no
        // g_ran, so the extra term cannot be absorbed.
        let params = Params::setup();
        let id = hash_identity(b"alice");
        let (tid, o_tid) = tid_for(&params, id);
        let forged = tag(&params, &id) + random_blinding() * params.pp.g_ran;

        let proof = TagProof::prove(&params, &tid, &forged, &o_tid, CTX);
        assert!(!proof.verify(&params, &tid, &forged, CTX));
    }

    #[test]
    fn single_equation_shortcut_accepts_a_forged_tag() {
        // Why Pi.Tag is not one call to the sigma engine. Fold the clauses with a
        // weight w fixed from (tid, tag) BEFORE t:
        //   tid + w*tag = id*(g_iden + w*g_tag) + s*g_ran
        // With tag' = id*g_tag + b*g_ran the right side becomes
        //   id*(g_iden + w*g_tag) + (s + w*b)*g_ran,
        // and the prover knows (id, s + w*b), so the engine accepts the forged tag.
        let params = Params::setup();
        let id = hash_identity(b"alice");
        let (tid, o_tid) = tid_for(&params, id);
        let b = random_blinding();
        let forged = tag(&params, &id) + b * params.pp.g_ran;

        let w = Challenge::new(b"test/fold", &params.pp).point(b"tid", &tid.0).point(b"tag", &forged).finish();
        let bases = [params.pp.g_iden + w * params.g_tag, params.pp.g_ran];
        let u = tid.0 + w * forged;
        let bind = |ch: Challenge| ch.point(b"u", &u);

        let folded = sigma::prove(&params.pp, b"test/fold", &bases, &[id, o_tid.blinding + w * b], bind);
        assert!(sigma::verify(&params.pp, b"test/fold", &bases, &u, &folded, bind));

        // The two-clause proof, for the same forged tag, does not go through.
        let proof = TagProof::prove(&params, &tid, &forged, &o_tid, CTX);
        assert!(!proof.verify(&params, &tid, &forged, CTX));
    }

    #[test]
    fn a_tid_holding_a_value_fails() {
        // Clause 1 has no g_val, so it also pins tid's value to 0.
        let params = Params::setup();
        let id = hash_identity(b"alice");
        let o_tid = Opening { id, val: Scalar::from(5u64), blinding: random_blinding() };
        let tid = commit(&params.pp, &o_tid);
        let t = tag(&params, &id);

        let proof = TagProof::prove(&params, &tid, &t, &o_tid, CTX);
        assert!(!proof.verify(&params, &tid, &t, CTX));
    }

    #[test]
    fn proof_is_bound_to_the_context() {
        let params = Params::setup();
        let id = hash_identity(b"alice");
        let (tid, o_tid) = tid_for(&params, id);
        let t = tag(&params, &id);

        let proof = TagProof::prove(&params, &tid, &t, &o_tid, b"round-1");
        assert!(!proof.verify(&params, &tid, &t, b"round-2"));
    }

    #[test]
    fn challenge_depends_on_every_input() {
        // Change any one input and c must change, otherwise that input is not bound.
        let params = Params::setup();
        let id = hash_identity(b"alice");
        let (tid, o_tid) = tid_for(&params, id);
        let t = tag(&params, &id);
        let p = TagProof::prove(&params, &tid, &t, &o_tid, CTX);
        let c = challenge(&params, &tid, &t, CTX, &p.t1, &p.t2);

        let x = random_blinding() * params.pp.g_val; // any other point
        let other_params = Params { g_tag: x, ..params };
        assert_ne!(c, challenge(&other_params, &tid, &t, CTX, &p.t1, &p.t2));
        assert_ne!(c, challenge(&params, &Commitment(x), &t, CTX, &p.t1, &p.t2));
        assert_ne!(c, challenge(&params, &tid, &x, CTX, &p.t1, &p.t2));
        assert_ne!(c, challenge(&params, &tid, &t, b"round-2", &p.t1, &p.t2));
        assert_ne!(c, challenge(&params, &tid, &t, CTX, &x, &p.t2));
        assert_ne!(c, challenge(&params, &tid, &t, CTX, &p.t1, &x));
    }

    #[test]
    fn merge_weight_depends_on_the_responses() {
        // If delta ignored z, the prover would know it before answering and could
        // solve the single merged equation without satisfying both clauses.
        let params = Params::setup();
        let id = hash_identity(b"alice");
        let (tid, o_tid) = tid_for(&params, id);
        let t = tag(&params, &id);
        let p = TagProof::prove(&params, &tid, &t, &o_tid, CTX);
        let delta = merge_weight(&params, &tid, &t, CTX, &p);

        let one = Scalar::ONE;
        for q in [TagProof { z_id: p.z_id + one, ..p }, TagProof { z_s: p.z_s + one, ..p }] {
            assert_ne!(delta, merge_weight(&params, &tid, &t, CTX, &q));
        }
    }

    #[test]
    fn merged_check_agrees_with_the_two_equations() {
        // verify() checks both clauses as one MSM. For an honest proof and for
        // tampered ones, it must give the textbook two-equation verdict.
        let params = Params::setup();
        let id = hash_identity(b"alice");
        let (tid, o_tid) = tid_for(&params, id);
        let t = tag(&params, &id);
        let honest = TagProof::prove(&params, &tid, &t, &o_tid, CTX);

        let x = random_blinding() * params.pp.g_val;
        let cases = [
            TagProof { ..honest },
            TagProof { t1: honest.t1 + x, ..honest },
            TagProof { t2: honest.t2 + x, ..honest },
            TagProof { z_id: honest.z_id + Scalar::ONE, ..honest },
            TagProof { z_s: honest.z_s + Scalar::ONE, ..honest },
        ];
        for (k, p) in cases.iter().enumerate() {
            let textbook = two_equations_hold(&params, p, &tid, &t, CTX);
            assert_eq!(p.verify(&params, &tid, &t, CTX), textbook, "case {k}");
            assert_eq!(textbook, k == 0, "case {k}");
        }
    }

    #[test]
    fn two_proofs_for_the_same_statement_differ() {
        // Fresh masks every time, so a proof does not repeat.
        let params = Params::setup();
        let id = hash_identity(b"alice");
        let (tid, o_tid) = tid_for(&params, id);
        let t = tag(&params, &id);
        let p1 = TagProof::prove(&params, &tid, &t, &o_tid, CTX);
        let p2 = TagProof::prove(&params, &tid, &t, &o_tid, CTX);
        assert_ne!(p1.t1, p2.t1);
    }

    #[test]
    fn proof_size_is_128_bytes() {
        // 2 points + 2 scalars.
        let params = Params::setup();
        let id = hash_identity(b"alice");
        let (tid, o_tid) = tid_for(&params, id);
        let p = TagProof::prove(&params, &tid, &tag(&params, &id), &o_tid, CTX);
        let size = p.t1.compress().to_bytes().len()
            + p.t2.compress().to_bytes().len()
            + p.z_id.as_bytes().len()
            + p.z_s.as_bytes().len();
        assert_eq!(size, 128);
    }
}
