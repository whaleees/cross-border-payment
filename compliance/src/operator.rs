use std::collections::HashSet;

use curve25519_dalek::ristretto::RistrettoPoint;
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use rand_core::OsRng;

use crate::hash::Fingerprint;
use crate::params::PERIOD_DAYS;

// One entry of the nullifier set. The kind is part of the key, so a registration
// tag can never be mistaken for a nullifier, or the other way round.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Entry {
    Nullifier([u8; 32]), // nf = H("nf", rho) of a spent state token
    Tag([u8; 32]),       // a registered user's tag, compressed
}

impl Entry {
    pub fn tag(t: &RistrettoPoint) -> Self {
        Entry::Tag(t.compress().to_bytes())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Insert {
    Inserted,
    AlreadyPresent, // the token was spent before, or the user registered before
}

// Append-only: insert_if_absent is the only write and nothing is ever removed
// (decision 19). Check and insert are one step: here one &mut call, which a shared
// lock serialises; in a database, a unique key on the entry.
#[derive(Clone, Debug, Default)]
pub struct NullifierSet {
    entries: HashSet<Entry>,
}

impl NullifierSet {
    pub fn contains(&self, e: &Entry) -> bool {
        self.entries.contains(e)
    }

    pub fn insert_if_absent(&mut self, e: Entry) -> Insert {
        if self.entries.insert(e) { Insert::Inserted } else { Insert::AlreadyPresent }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

// One verifier as the operator lists it: its key number, its public key, and its
// limit B in SGD cents (decision 19c).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierEntry {
    pub kid: u32,
    pub pk: VerifyingKey,
    pub limit: u64,
}

// The registry the prover checks every request against: T and every verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Registry {
    pub period_days: u32,
    pub verifiers: Vec<VerifierEntry>,
}

impl Registry {
    pub fn get(&self, kid: u32) -> Option<&VerifierEntry> {
        self.verifiers.iter().find(|v| v.kid == kid)
    }

    // H("registry", T, count, (kid, pk, B) for each verifier)
    pub fn digest(&self) -> [u8; 32] {
        self.verifiers
            .iter()
            .fold(
                Fingerprint::new(b"registry").u32(self.period_days).u32(self.verifiers.len() as u32),
                |h, v| h.u32(v.kid).fixed(v.pk.as_bytes()).u64(v.limit),
            )
            .finish()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignedRegistry {
    pub registry: Registry,
    pub sig: Signature,
}

impl SignedRegistry {
    // G0 step 12: the prover and every verifier accept the registry only under the
    // operator's key.
    pub fn verify(&self, operator_pk: &VerifyingKey) -> bool {
        operator_pk.verify_strict(&self.registry.digest(), &self.sig).is_ok()
    }
}

// The operator (G10): runs the nullifier set and signs the registry.
pub struct Operator {
    sk: SigningKey,
    verifiers: Vec<VerifierEntry>,
    pub ns: NullifierSet,
}

impl Operator {
    pub fn new() -> Self {
        Operator { sk: SigningKey::generate(&mut OsRng), verifiers: Vec::new(), ns: NullifierSet::default() }
    }

    pub fn public_key(&self) -> VerifyingKey {
        self.sk.verifying_key()
    }

    // G0 step 9. A kid names exactly one verifier, so a taken kid is refused.
    pub fn register(&mut self, kid: u32, pk: VerifyingKey, limit: u64) -> bool {
        if self.verifiers.iter().any(|v| v.kid == kid) {
            return false;
        }
        self.verifiers.push(VerifierEntry { kid, pk, limit });
        true
    }

    // G0 steps 10-11.
    pub fn publish(&self) -> SignedRegistry {
        let registry = Registry { period_days: PERIOD_DAYS, verifiers: self.verifiers.clone() };
        let sig = self.sk.sign(&registry.digest());
        SignedRegistry { registry, sig }
    }
}

impl Default for Operator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Mutex};
    use std::thread;

    const SINGAPORE: u32 = 1;
    const THAILAND: u32 = 2;

    fn operator_with_two_verifiers() -> Operator {
        let mut op = Operator::new();
        assert!(op.register(SINGAPORE, SigningKey::generate(&mut OsRng).verifying_key(), 500_000));
        assert!(op.register(THAILAND, SigningKey::generate(&mut OsRng).verifying_key(), 300_000));
        op
    }

    #[test]
    fn an_entry_is_recorded_once() {
        // A spent token: the first verifier records nf, any later one is refused.
        let mut ns = NullifierSet::default();
        let nf = Entry::Nullifier([7; 32]);
        assert!(!ns.contains(&nf));
        assert_eq!(ns.insert_if_absent(nf), Insert::Inserted);
        assert!(ns.contains(&nf));
        assert_eq!(ns.insert_if_absent(nf), Insert::AlreadyPresent);
        assert_eq!(ns.len(), 1);
    }

    #[test]
    fn a_tag_and_a_nullifier_with_the_same_bytes_are_different_entries() {
        let mut ns = NullifierSet::default();
        assert_eq!(ns.insert_if_absent(Entry::Nullifier([7; 32])), Insert::Inserted);
        assert!(!ns.contains(&Entry::Tag([7; 32])));
        assert_eq!(ns.insert_if_absent(Entry::Tag([7; 32])), Insert::Inserted);
    }

    #[test]
    fn concurrent_inserts_of_one_nullifier_let_exactly_one_through() {
        // The same token presented to eight verifiers at once (G7 step 4): exactly
        // one records its nullifier, the other seven reject the round.
        let ns = Arc::new(Mutex::new(NullifierSet::default()));
        let handles: Vec<_> = (0..8)
            .map(|_| {
                let ns = Arc::clone(&ns);
                thread::spawn(move || ns.lock().unwrap().insert_if_absent(Entry::Nullifier([9; 32])))
            })
            .collect();
        let results: Vec<Insert> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        assert_eq!(results.iter().filter(|r| **r == Insert::Inserted).count(), 1);
    }

    #[test]
    fn the_published_registry_verifies_under_the_operators_key() {
        let op = operator_with_two_verifiers();
        let signed = op.publish();
        assert!(signed.verify(&op.public_key()));
        assert_eq!(signed.registry.period_days, 365);
        assert_eq!(signed.registry.get(THAILAND).unwrap().limit, 300_000);
        assert!(signed.registry.get(99).is_none());
    }

    #[test]
    fn changing_any_limit_breaks_the_signature() {
        // A verifier, or anyone between it and the prover, rewrites its B to probe
        // the user's total (G3 step 7). The registry no longer verifies.
        let op = operator_with_two_verifiers();
        let mut signed = op.publish();
        signed.registry.verifiers[0].limit = 1_000;
        assert!(!signed.verify(&op.public_key()));
    }

    #[test]
    fn changing_the_period_or_a_key_breaks_the_signature() {
        let op = operator_with_two_verifiers();
        let mut longer = op.publish();
        longer.registry.period_days = 30;
        assert!(!longer.verify(&op.public_key()));

        let mut swapped = op.publish();
        swapped.registry.verifiers[1].pk = SigningKey::generate(&mut OsRng).verifying_key();
        assert!(!swapped.verify(&op.public_key()));
    }

    #[test]
    fn a_registry_signed_by_someone_else_fails() {
        let op = operator_with_two_verifiers();
        let other = Operator::new();
        assert!(!op.publish().verify(&other.public_key()));
    }

    #[test]
    fn a_taken_kid_is_refused() {
        let mut op = operator_with_two_verifiers();
        assert!(!op.register(SINGAPORE, SigningKey::generate(&mut OsRng).verifying_key(), 1));
        assert_eq!(op.publish().registry.verifiers.len(), 2);
    }
}
