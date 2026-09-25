use curve25519_dalek::{
    RistrettoPoint, Scalar,
    traits::{Identity, VartimeMultiscalarMul},
};

use crate::commitment::Commitment;
use crate::ideq::{IdEqProof, challenge as ideq_challenge};
use crate::params::PublicParams;
use crate::transcript::Challenge;

pub struct BatchItem<'a> {
    pub c0: Commitment,
    pub c1: Commitment,
    pub ctx: &'a [u8],
    pub proof: IdEqProof,
}

fn weights(pp: &PublicParams, items: &[BatchItem]) -> Vec<Scalar> {
    let mut ch = Challenge::new(b"IBC/v1/BatchVer", pp);
    for it in items {
        ch = ch
            .point(b"c0", &it.c0.0)
            .point(b"c1", &it.c1.0)
            .bytes(b"ctx", it.ctx)
            .point(b"t", &it.proof.t)
            .scalar(b"zv", &it.proof.z_val)
            .scalar(b"zr", &it.proof.z_ran);
    }
    (0..items.len()).map(|_| ch.challenge_scalar(b"delta")).collect()
}

pub fn batch_verify(pp: &PublicParams, items: &[BatchItem]) -> bool {
    let m = items.len();
    if m == 0 {
        return true;
    }

    // Per-proof beta_j and D_j (public).
    let mut betas = Vec::with_capacity(m);
    let mut ds = Vec::with_capacity(m);
    for it in items {
        betas.push(ideq_challenge(pp, &it.c0, &it.c1, it.ctx, &it.proof.t));
        ds.push(it.c0.0 - it.c1.0);
    }

    let deltas = weights(pp, items);

    // Z_val = sum delta_j z_val_j ; Z_ran = sum delta_j z_ran_j
    let z_val: Scalar = items.iter().zip(&deltas).map(|(it, d)| *d * it.proof.z_val).sum();
    let z_ran: Scalar = items.iter().zip(&deltas).map(|(it, d)| *d * it.proof.z_ran).sum();

    // One MSM over 2m + 2 bases; accept iff it is the identity point.
    //   Z_val*g_val + Z_ran*g_ran - sum delta_j*t_j - sum (delta_j*beta_j)*D_j == 0
    let mut scalars = Vec::with_capacity(2 + 2 * m);
    let mut points = Vec::with_capacity(2 + 2 * m);
    scalars.push(z_val);
    points.push(pp.g_val);
    scalars.push(z_ran);
    points.push(pp.g_ran);
    for i in 0..m {
        scalars.push(-deltas[i]);
        points.push(items[i].proof.t);
        scalars.push(-(deltas[i] * betas[i]));
        points.push(ds[i]);
    }

    RistrettoPoint::vartime_multiscalar_mul(scalars, points) == RistrettoPoint::identity()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commitment::{Opening, commit, random_blinding};
    use crate::params::{hash_identity, value_to_scalar};

    // A valid Π.IDEq item (two commitments sharing an identity).
    fn valid_item(ctx: &'static [u8]) -> BatchItem<'static> {
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let o0 = Opening { id, val: value_to_scalar(100), blinding: random_blinding() };
        let o1 = Opening { id, val: value_to_scalar(250), blinding: random_blinding() };
        let c0 = commit(&pp, &o0);
        let c1 = commit(&pp, &o1);
        let proof = IdEqProof::prove(&pp, &c0, &c1, &o0, &o1, ctx);
        BatchItem { c0, c1, ctx, proof }
    }

    // Field-by-field copy (IdEqProof is not Clone).
    fn copy<'a>(it: &BatchItem<'a>) -> BatchItem<'a> {
        let proof = IdEqProof { t: it.proof.t, z_val: it.proof.z_val, z_ran: it.proof.z_ran };
        BatchItem { c0: it.c0, c1: it.c1, ctx: it.ctx, proof }
    }

    fn individually_valid(pp: &PublicParams, it: &BatchItem) -> bool {
        it.proof.verify(pp, &it.c0, &it.c1, it.ctx)
    }

    #[test]
    fn all_valid_batch_accepts() {
        let pp = PublicParams::setup();
        let items = vec![valid_item(b"a"), valid_item(b"b"), valid_item(b"c")];
        assert!(batch_verify(&pp, &items));
    }

    #[test]
    fn one_bad_proof_rejects() {
        // Corrupt one response, in each position in turn.
        let pp = PublicParams::setup();
        for bad in 0..3 {
            let mut items = vec![valid_item(b"a"), valid_item(b"b"), valid_item(b"c")];
            items[bad].proof.z_val += Scalar::ONE;
            assert!(!batch_verify(&pp, &items), "bad proof at position {}", bad + 1);
        }
    }

    #[test]
    fn empty_batch_accepts() {
        let pp = PublicParams::setup();
        assert!(batch_verify(&pp, &[]));
    }

    #[test]
    fn single_proof_batch_matches() {
        let pp = PublicParams::setup();
        let items = vec![valid_item(b"solo")];
        assert!(batch_verify(&pp, &items));
        // Agrees with the individual verifier.
        assert!(individually_valid(&pp, &items[0]));
    }

    #[test]
    fn wrong_ctx_in_one_item_rejects() {
        // Build a valid proof, then change the item's ctx: beta_j won't match.
        let pp = PublicParams::setup();
        let mut it = valid_item(b"right");
        it.ctx = b"wrong";
        let items = vec![it];
        assert!(!batch_verify(&pp, &items));
    }

    #[test]
    fn batch_agrees_with_individual() {
        // A mix of valid and tampered proofs: batch == AND of individual verifies.
        let pp = PublicParams::setup();
        let mut items = vec![valid_item(b"a"), valid_item(b"b"), valid_item(b"c")];
        items[2].proof.z_ran += Scalar::ONE; // tamper the third

        let individual_all = items.iter().all(|it| individually_valid(&pp, it));
        assert_eq!(batch_verify(&pp, &items), individual_all);
        assert!(!individual_all); // sanity: the mix really contains a bad one
    }

    #[test]
    fn errors_cannot_be_made_to_cancel() {
        let pp = PublicParams::setup();
        let mut items = vec![valid_item(b"a"), valid_item(b"b"), valid_item(b"c")];
        let d = weights(&pp, &items);
        let k = random_blinding();
        items[0].proof.z_val += k * d[0].invert();
        items[1].proof.z_val -= k * d[1].invert();

        assert!(!individually_valid(&pp, &items[0]) && !individually_valid(&pp, &items[1]));
        assert!(!batch_verify(&pp, &items));
    }

    #[test]
    fn weights_depend_on_every_part_of_every_item() {
        let pp = PublicParams::setup();
        let items = vec![valid_item(b"a"), valid_item(b"b"), valid_item(b"c")];
        let base = weights(&pp, &items);
        assert!(base[0] != base[1] && base[1] != base[2] && base[0] != base[2]);

        let x = random_blinding() * pp.g_iden; // any other point
        let s = random_blinding(); // any other scalar
        for j in 0..items.len() {
            for field in 0..6 {
                let mut changed: Vec<BatchItem> = items.iter().map(copy).collect();
                let it = &mut changed[j];
                match field {
                    0 => it.c0 = Commitment(x),
                    1 => it.c1 = Commitment(x),
                    2 => it.ctx = b"other",
                    3 => it.proof.t = x,
                    4 => it.proof.z_val = s,
                    _ => it.proof.z_ran = s,
                }
                for (old, new) in base.iter().zip(weights(&pp, &changed)) {
                    assert_ne!(*old, new, "item {}, field {} not bound", j + 1, field);
                }
            }
        }
    }
}
