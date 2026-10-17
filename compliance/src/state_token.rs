use curve25519_dalek::ristretto::CompressedRistretto;
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use rand_core::{OsRng, RngCore};

use crate::hash::Fingerprint;

// The state token K = (kid, cm, sigma): a verifier's signature over the user's list
// of commitment pairs and over cm, the hidden form of a secret rho.
//   cm = H("cm", rho)   signed now, without the verifier learning rho
//   nf = H("nf", rho)   revealed when the token is spent, recorded by the operator
// A token proves the list is complete and current only together with the nullifier
// set: the list is the one a verifier approved, and no newer token replaced it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateToken {
    pub kid: u32,      // which verifier signed, looked up in the operator's registry
    pub cm: [u8; 32],  // nullifier commitment
    pub sig: Signature,
}

// A fresh nullifier preimage, chosen by the prover when it asks for a new token.
pub fn fresh_preimage() -> [u8; 32] {
    let mut rho = [0u8; 32];
    OsRng.fill_bytes(&mut rho);
    rho
}

pub fn nullifier_commitment(rho: &[u8; 32]) -> [u8; 32] {
    Fingerprint::new(b"cm").fixed(rho).finish()
}

pub fn nullifier(rho: &[u8; 32]) -> [u8; 32] {
    Fingerprint::new(b"nf").fixed(rho).finish()
}

// h = H("state", c_1 || d_1 || ... || c_N || d_N || cm). The pairs go in, in order,
// so dropping, adding, reordering or re-pairing any of them changes h. The lists come
// compressed (hash::compress): the round already has them that way for stmt.
pub fn state_hash(cs: &[CompressedRistretto], ds: &[CompressedRistretto], cm: &[u8; 32]) -> [u8; 32] {
    assert_eq!(cs.len(), ds.len(), "every value commitment has a date commitment");
    cs.iter()
        .zip(ds)
        .fold(Fingerprint::new(b"state"), |h, (c, d)| h.fixed(c.as_bytes()).fixed(d.as_bytes()))
        .fixed(cm)
        .finish()
}

impl StateToken {
    // G7 steps 1-2: the verifier signs the front it has just approved.
    pub fn issue(sk: &SigningKey, kid: u32, cs: &[CompressedRistretto], ds: &[CompressedRistretto], cm: [u8; 32]) -> Self {
        StateToken { kid, cm, sig: sk.sign(&state_hash(cs, ds, &cm)) }
    }

    // G6 steps 2-3: exactly this list, in this order, was signed with pk.
    // The caller finds pk by kid in the registry.
    pub fn verify(&self, pk: &VerifyingKey, cs: &[CompressedRistretto], ds: &[CompressedRistretto]) -> bool {
        if cs.len() != ds.len() {
            return false;
        }
        pk.verify_strict(&state_hash(cs, ds, &self.cm), &self.sig).is_ok()
    }

    // G6 steps 4-5: rho must open cm. Returns the nullifier, which the verifier
    // then checks against, and finally records in, the nullifier set.
    pub fn open(&self, rho: &[u8; 32]) -> Option<[u8; 32]> {
        (nullifier_commitment(rho) == self.cm).then(|| nullifier(rho))
    }

    pub fn to_bytes(&self) -> [u8; 100] {
        let mut out = [0u8; 100];
        out[0..4].copy_from_slice(&self.kid.to_le_bytes());
        out[4..36].copy_from_slice(&self.cm);
        out[36..100].copy_from_slice(&self.sig.to_bytes());
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::compress;
    use ibc::commitment::{Commitment, Opening, commit, random_blinding};
    use ibc::params::{PublicParams, hash_identity, value_to_scalar};
    use std::collections::HashSet;

    const SINGAPORE: u32 = 1;
    const THAILAND: u32 = 2;

    type List = (Vec<CompressedRistretto>, Vec<CompressedRistretto>);

    // n pairs of alice's commitments (amount, date), compressed as a round hashes them.
    fn pairs(pp: &PublicParams, n: u64) -> List {
        let id = hash_identity(b"alice");
        let cs: Vec<Commitment> = (0..n)
            .map(|k| commit(pp, &Opening { id, val: value_to_scalar(100 + k), blinding: random_blinding() }))
            .collect();
        let ds: Vec<Commitment> = (0..n)
            .map(|k| Commitment(value_to_scalar(20_000 + k) * pp.g_val + random_blinding() * pp.g_ran))
            .collect();
        (compress(&cs), compress(&ds))
    }

    // state_token.md section 6. January, Singapore: K1 over L1 (one pair).
    // March, Thailand: K1 spent, K2 issued over L2 (three pairs).
    struct Story {
        l1: List,
        l2: List,
        k1: StateToken,
        k2: StateToken,
        rho1: [u8; 32],
        rho2: [u8; 32],
        sg: SigningKey,
        th: SigningKey,
        spent: HashSet<[u8; 32]>, // stands in for the operator's nullifier set
    }

    fn story() -> Story {
        let pp = PublicParams::setup();
        let (sg, th) = (SigningKey::generate(&mut OsRng), SigningKey::generate(&mut OsRng));
        let (l1, l2) = (pairs(&pp, 1), pairs(&pp, 3));
        let (rho1, rho2) = (fresh_preimage(), fresh_preimage());
        let k1 = StateToken::issue(&sg, SINGAPORE, &l1.0, &l1.1, nullifier_commitment(&rho1));
        let k2 = StateToken::issue(&th, THAILAND, &l2.0, &l2.1, nullifier_commitment(&rho2));

        // Thailand accepted K1 in March: its nullifier is recorded.
        let mut spent = HashSet::new();
        spent.insert(k1.open(&rho1).unwrap());
        Story { l1, l2, k1, k2, rho1, rho2, sg, th, spent }
    }

    // Every check a verifier runs on a presented token (G6 steps 2-5).
    fn accepted(s: &Story, pk: &VerifyingKey, k: &StateToken, list: &List, rho: &[u8; 32]) -> bool {
        k.verify(pk, &list.0, &list.1) && k.open(rho).is_some_and(|nf| !s.spent.contains(&nf))
    }

    #[test]
    fn f_the_honest_current_token_is_accepted() {
        let s = story();
        assert!(accepted(&s, &s.th.verifying_key(), &s.k2, &s.l2, &s.rho2));
    }

    #[test]
    fn a_an_old_token_is_caught_by_its_nullifier() {
        // L1 with K1: signature and opening are fine, but K1 was spent in March.
        let s = story();
        assert!(s.k1.verify(&s.sg.verifying_key(), &s.l1.0, &s.l1.1));
        assert!(!accepted(&s, &s.sg.verifying_key(), &s.k1, &s.l1, &s.rho1));
    }

    #[test]
    fn b_an_old_list_under_the_new_token_fails_the_signature() {
        let s = story();
        assert!(!accepted(&s, &s.th.verifying_key(), &s.k2, &s.l1, &s.rho2));
    }

    #[test]
    fn c_a_list_missing_one_pair_fails_the_signature() {
        let s = story();
        let shorter = (s.l2.0[..2].to_vec(), s.l2.1[..2].to_vec());
        assert!(!accepted(&s, &s.th.verifying_key(), &s.k2, &shorter, &s.rho2));
    }

    #[test]
    fn d_a_different_rho_does_not_open_cm() {
        // A different rho would give a different, unrecorded nullifier.
        let s = story();
        assert!(s.k2.open(&fresh_preimage()).is_none());
        assert!(!accepted(&s, &s.th.verifying_key(), &s.k2, &s.l2, &fresh_preimage()));
    }

    #[test]
    fn e_a_token_signed_by_the_prover_itself_fails() {
        // PayPay signs L1 with its own key and claims it came from Thailand.
        let s = story();
        let paypay = SigningKey::generate(&mut OsRng);
        let rho = fresh_preimage();
        let forged = StateToken::issue(&paypay, THAILAND, &s.l1.0, &s.l1.1, nullifier_commitment(&rho));
        assert!(!accepted(&s, &s.th.verifying_key(), &forged, &s.l1, &rho));
    }

    #[test]
    fn g_the_current_token_cannot_be_spent_twice() {
        let mut s = story();
        let nf2 = s.k2.open(&s.rho2).unwrap();
        assert!(s.spent.insert(nf2)); // first use (attempt f) records nf2
        assert!(!accepted(&s, &s.th.verifying_key(), &s.k2, &s.l2, &s.rho2));
    }

    #[test]
    fn reordering_or_repairing_the_list_fails() {
        // The order is signed, and so is which date goes with which amount.
        let s = story();
        let pk = s.th.verifying_key();
        let (cs, ds) = &s.l2;
        let reordered = (vec![cs[1], cs[0], cs[2]], vec![ds[1], ds[0], ds[2]]);
        let repaired = (cs.clone(), vec![ds[1], ds[0], ds[2]]);
        assert!(!s.k2.verify(&pk, &reordered.0, &reordered.1));
        assert!(!s.k2.verify(&pk, &repaired.0, &repaired.1));
    }

    #[test]
    fn mismatched_list_lengths_are_rejected_not_truncated() {
        let s = story();
        let (cs, ds) = &s.l2;
        assert!(!s.k2.verify(&s.th.verifying_key(), cs, &ds[..2]));
    }

    #[test]
    fn the_signer_cannot_compute_the_nullifier_from_cm() {
        // The verifier that signs K2 sees cm2 only. nf2 is a different hash of rho2,
        // so watching the nullifier set does not tell it when K2 is spent.
        let s = story();
        let nf2 = s.k2.open(&s.rho2).unwrap();
        assert_ne!(s.k2.cm, nf2);
        assert_eq!(nf2, nullifier(&s.rho2));
    }

    #[test]
    fn token_is_100_bytes() {
        let s = story();
        let b = s.k2.to_bytes();
        assert_eq!(b.len(), 100);
        assert_eq!(b[0..4], THAILAND.to_le_bytes());
        assert_eq!(b[4..36], s.k2.cm);
    }
}
