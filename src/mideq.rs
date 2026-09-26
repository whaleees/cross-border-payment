use curve25519_dalek::{RistrettoPoint, Scalar};

use crate::commitment::{Commitment, Opening};
use crate::params::PublicParams;
use crate::sigma::{self, SigmaProof};
use crate::transcript::Challenge;

pub struct MIDEqProof(pub SigmaProof);

const DS: &[u8] = b"IBC/v1/MIDEq";
const DS_GAMMA: &[u8] = b"IBC/v1/MIDEq-gamma";

fn gammas(pp: &PublicParams, commits: &[Commitment], ctx: &[u8]) -> Vec<Scalar> {
    let base = commits
        .iter()
        .fold(Challenge::new(DS_GAMMA, pp), |ch, c| ch.point(b"c", &c.0))
        .bytes(b"ctx", ctx);
    (2..=commits.len())
        .map(|i| base.clone().bytes(b"i", &(i as u64).to_le_bytes()).finish())
        .collect()
}

// D = sum_{i>=2} gamma_i*(c1 - ci) = (sum gamma_i)*c1 - sum gamma_i*ci, kept as n
// terms so the engine folds it into its single MSM: the spec's one MSM of n + 3
// bases (g_val, g_ran, t, c1..cn).
fn target_d(pp: &PublicParams, commits: &[Commitment], ctx: &[u8]) -> Vec<(Scalar, RistrettoPoint)> {
    let g = gammas(pp, commits, ctx);
    let mut terms = Vec::with_capacity(commits.len());
    terms.push((g.iter().sum::<Scalar>(), commits[0].0)); // c1
    terms.extend(g.iter().zip(&commits[1..]).map(|(gi, ci)| (-gi, ci.0))); // c2..cn
    terms
}

// The main challenge binds all commitments + ctx (the engine appends t).
fn bind<'a>(commits: &'a [Commitment], ctx: &'a [u8]) -> impl FnOnce(Challenge) -> Challenge + 'a {
    move |ch| {
        let ch = commits.iter().fold(ch, |ch, c| ch.point(b"c", &c.0));
        ch.bytes(b"ctx", ctx)
    }
}

impl MIDEqProof {
    pub fn prove(
        pp: &PublicParams,
        commits: &[Commitment],
        openings: &[Opening],
        ctx: &[u8],
    ) -> Self {
        assert_eq!(commits.len(), openings.len());
        assert!(commits.len() >= 2, "MIDEq needs n >= 2");

        let o1 = &openings[0];
        let mut dv = Scalar::ZERO;
        let mut dr = Scalar::ZERO;
        for (g, oi) in gammas(pp, commits, ctx).iter().zip(&openings[1..]) {
            dv += g * (o1.val - oi.val);
            dr += g * (o1.blinding - oi.blinding);
        }

        let sp = sigma::prove(pp, DS, &[pp.g_val, pp.g_ran], &[dv, dr], bind(commits, ctx));
        MIDEqProof(sp)
    }

    pub fn verify(&self, pp: &PublicParams, commits: &[Commitment], ctx: &[u8]) -> bool {
        if commits.len() < 2 {
            return false;
        }
        let d = target_d(pp, commits, ctx);
        sigma::verify_terms(pp, DS, &[pp.g_val, pp.g_ran], &d, &self.0, bind(commits, ctx))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commitment::{commit, random_blinding};
    use crate::params::{hash_identity, value_to_scalar};

    // n commitments, all the given identity, each a different value and blinding.
    fn commitments(pp: &PublicParams, id_label: &[&[u8]]) -> (Vec<Commitment>, Vec<Opening>) {
        let mut cs = Vec::new();
        let mut os = Vec::new();
        for (k, lbl) in id_label.iter().enumerate() {
            let o = Opening {
                id: hash_identity(lbl),
                val: value_to_scalar(100 + k as u64),
                blinding: random_blinding(),
            };
            cs.push(commit(pp, &o));
            os.push(o);
        }
        (cs, os)
    }

    #[test]
    fn all_same_identity_verifies() {
        let pp = PublicParams::setup();
        let labels: Vec<&[u8]> = vec![b"alice", b"alice", b"alice", b"alice", b"alice"];
        let (cs, os) = commitments(&pp, &labels);
        let proof = MIDEqProof::prove(&pp, &cs, &os, b"batch-1");
        assert!(proof.verify(&pp, &cs, b"batch-1"));
    }

    #[test]
    fn a_different_identity_in_any_position_fails() {
        // One mallory among alices, tried in every position -- including first and
        // last, where an off-by-one in the loops over 2..=n would hide it.
        let pp = PublicParams::setup();
        for pos in 0..5 {
            let mut labels: Vec<&[u8]> = vec![b"alice" as &[u8]; 5];
            labels[pos] = b"mallory";
            let (cs, os) = commitments(&pp, &labels);
            let proof = MIDEqProof::prove(&pp, &cs, &os, b"batch-1");
            assert!(!proof.verify(&pp, &cs, b"batch-1"), "mallory at position {}", pos + 1);
        }
    }

    #[test]
    fn n_equals_2_verifies() {
        let pp = PublicParams::setup();
        let labels: Vec<&[u8]> = vec![b"alice", b"alice"];
        let (cs, os) = commitments(&pp, &labels);
        let proof = MIDEqProof::prove(&pp, &cs, &os, b"batch-1");
        assert!(proof.verify(&pp, &cs, b"batch-1"));
    }

    #[test]
    fn proof_is_constant_size() {
        let pp = PublicParams::setup();
        let small: Vec<&[u8]> = vec![b"alice", b"alice"];
        let (cs2, os2) = commitments(&pp, &small);
        let p2 = MIDEqProof::prove(&pp, &cs2, &os2, b"b");

        let big_labels: Vec<&[u8]> = (0..100).map(|_| b"alice" as &[u8]).collect();
        let (cs100, os100) = commitments(&pp, &big_labels);
        let p100 = MIDEqProof::prove(&pp, &cs100, &os100, b"b");

        assert_eq!(p2.0.z.len(), 2);
        assert_eq!(p100.0.z.len(), 2); // 96 bytes regardless of n
    }

    #[test]
    fn proof_is_bound_to_the_context() {
        let pp = PublicParams::setup();
        let labels: Vec<&[u8]> = vec![b"alice", b"alice", b"alice"];
        let (cs, os) = commitments(&pp, &labels);
        let proof = MIDEqProof::prove(&pp, &cs, &os, b"batch-1");
        assert!(!proof.verify(&pp, &cs, b"batch-2"));
    }

    #[test]
    fn reordering_commitments_fails() {
        // Prove for [c1,c2,c3], verify against [c1,c3,c2]. Reordering pairs the
        // weights with different differences, so D changes even if the gammas did
        // not -- this test would pass with gamma = 1. The gammas' binding is tested
        // by every_hash_binds_every_commitment.
        let pp = PublicParams::setup();
        let labels: Vec<&[u8]> = vec![b"alice", b"alice", b"alice"];
        let (cs, os) = commitments(&pp, &labels);
        let proof = MIDEqProof::prove(&pp, &cs, &os, b"batch-1");

        let reordered = vec![cs[0], cs[2], cs[1]];
        assert!(!proof.verify(&pp, &reordered, b"batch-1"));
    }

    #[test]
    fn every_hash_binds_every_commitment() {
        // Spec steps 1 and 5: each gamma_i and the challenge hash ALL of c1..cn and
        // ctx, and gamma_i also hashes i. So the gammas differ from each other, and
        // changing any one commitment (or ctx) changes every gamma and the challenge.
        let pp = PublicParams::setup();
        let labels: Vec<&[u8]> = vec![b"alice" as &[u8]; 4];
        let (cs, _) = commitments(&pp, &labels);
        let hashes = |cs: &[Commitment], ctx: &[u8]| -> Vec<Scalar> {
            let mut h = gammas(&pp, cs, ctx);
            h.push(bind(cs, ctx)(Challenge::new(DS, &pp)).finish());
            h
        };
        let base = hashes(&cs, b"batch-1");
        assert!(base[0] != base[1] && base[1] != base[2] && base[0] != base[2]);

        for j in 0..cs.len() {
            let mut changed = cs.clone();
            changed[j] = Commitment(random_blinding() * pp.g_iden);
            for (old, new) in base.iter().zip(hashes(&changed, b"batch-1")) {
                assert_ne!(*old, new, "commitment {} not bound", j + 1);
            }
        }
        for (old, new) in base.iter().zip(hashes(&cs, b"batch-2")) {
            assert_ne!(*old, new, "ctx not bound");
        }
    }

    #[test]
    fn identities_cannot_be_made_to_cancel() {
        // The attack the spec warns about (§2, implementation requirement). If
        // mallory knew the gammas before fixing the commitments, she could pick two
        // identities that are NOT alice's but whose differences cancel:
        //   gamma_2*(id1 - id2) + gamma_3*(id1 - id3) = 0
        // Then D has no g_iden term and the proof goes through. She tries: compute
        // the gammas on a draft set, solve for id3, commit. Because every gamma
        // hashes every commitment, committing to id3 changes the gammas and the
        // cancellation breaks.
        let pp = PublicParams::setup();
        let ctx: &[u8] = b"batch-1";
        let id1 = hash_identity(b"alice");
        let id2 = hash_identity(b"mallory");
        let o1 = Opening { id: id1, val: value_to_scalar(100), blinding: random_blinding() };
        let o2 = Opening { id: id2, val: value_to_scalar(101), blinding: random_blinding() };
        let draft = Opening { id: id1, val: value_to_scalar(102), blinding: random_blinding() };
        let (c1, c2) = (commit(&pp, &o1), commit(&pp, &o2));
        let g = gammas(&pp, &[c1, c2, commit(&pp, &draft)], ctx); // [gamma_2, gamma_3]

        let id3 = id1 + g[0] * (id1 - id2) * g[1].invert(); // cancels for the draft gammas
        let o3 = Opening { id: id3, ..draft };
        let cs = [c1, c2, commit(&pp, &o3)];

        let proof = MIDEqProof::prove(&pp, &cs, &[o1, o2, o3], ctx);
        assert!(!proof.verify(&pp, &cs, ctx));
    }

    #[test]
    fn gammas_match_the_spec_formula() {
        // gammas() hashes c1..cn once and copies that state for each i. That must
        // give exactly the spec's gamma_i = H(ds_gamma, pp, c1..cn, ctx, i),
        // computed here the slow way: a fresh hash per i.
        let pp = PublicParams::setup();
        let labels: Vec<&[u8]> = vec![b"alice" as &[u8]; 5];
        let (cs, _) = commitments(&pp, &labels);
        let fast = gammas(&pp, &cs, b"batch-1");
        for i in 2..=cs.len() {
            let slow = cs
                .iter()
                .fold(Challenge::new(DS_GAMMA, &pp), |ch, c| ch.point(b"c", &c.0))
                .bytes(b"ctx", b"batch-1")
                .bytes(b"i", &(i as u64).to_le_bytes())
                .finish();
            assert_eq!(fast[i - 2], slow, "gamma_{i}");
        }
    }
}
