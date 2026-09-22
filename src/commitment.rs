use core::ops::{Add, Sub};

use curve25519_dalek::{RistrettoPoint, Scalar, ristretto::CompressedRistretto};
use rand_core::OsRng;

use crate::params::PublicParams;

//The opening of a commitment: everything the prover keeps secret
#[derive(Clone, Copy, Debug)]
pub struct Opening {
    pub id: Scalar,
    pub val: Scalar,
    pub blinding: Scalar,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Commitment(pub RistrettoPoint);

// Sample a fresh blinding factor 
pub fn random_blinding() -> Scalar {
    Scalar::random(&mut OsRng)
}

// Commit
pub fn commit(pp: &PublicParams, o: &Opening) -> Commitment
{
    Commitment(o.id * pp.g_iden + o.val * pp.g_val + o.blinding * pp.g_ran)
}

// Recompute and compare
pub fn verify(pp: &PublicParams, c: &Commitment, o: &Opening) -> bool
{
    commit(pp, o) == *c 
}

impl Commitment {
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.compress().to_bytes()
    }

    pub fn from_bytes(bytes: &[u8; 32]) -> Option<Commitment>
    {
        CompressedRistretto::from_slice(bytes)
            .ok()?
            .decompress()
            .map(Commitment)
    }
}

impl Add for Commitment {
    type Output = Commitment;
    
    fn add(self, rhs: Commitment) -> Commitment
    {
        Commitment(self.0 + rhs.0)
    }
}

impl Sub for Commitment {
    type Output = Commitment;

    fn sub(self, rhs: Commitment) -> Commitment
    {
        Commitment(self.0 - rhs.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::params::{hash_identity, value_to_scalar};

    fn sample() -> (PublicParams, Opening) {
        let pp = PublicParams::setup();
        let o = Opening {
            id: hash_identity(b"user_42"),
            val: value_to_scalar(1_500),
            blinding: random_blinding(),
        };
        (pp, o)
    }

    #[test]
    fn commit_then_verify() {
        let (pp, o) = sample();
        let c = commit(&pp, &o);
        assert!(verify(&pp, &c, &o));
    }

    #[test]
    fn wrong_blinding_fails() {
        let (pp, o) = sample();
        let c = commit(&pp, &o);
        let bad = Opening { blinding: random_blinding(), ..o };
        assert!(!verify(&pp, &c, &bad));
    }

    #[test]
    fn wrong_value_fails() {
        let (pp, o) = sample();
        let c = commit(&pp, &o);
        let bad = Opening { val: value_to_scalar(9_999), ..o };
        assert!(!verify(&pp, &c, &bad));
    }

    #[test]
    fn wrong_identity_fails() {
        let (pp, o) = sample();
        let c = commit(&pp, &o);
        let bad = Opening { id: hash_identity(b"user_43"), ..o };
        assert!(!verify(&pp, &c, &bad));
    }

    #[test]
    fn hiding_same_opening_different_blinding_differs() {
        let (pp, o) = sample();
        let a = commit(&pp, &o);
        let b = commit(&pp, &Opening { blinding: random_blinding(), ..o });
        assert_ne!(a, b);
    }

    #[test]
    fn bytes_roundtrip() {
        let (pp, o) = sample();
        let c = commit(&pp, &o);
        assert_eq!(Commitment::from_bytes(&c.to_bytes()), Some(c));
    }

    #[test]
    fn homomorphism_holds() {
        // Commitments add componentwise: this is what makes c0 - c1 in step 04
        // cancel the identity term.
        let pp = PublicParams::setup();
        let o1 = Opening { id: hash_identity(b"a"), val: value_to_scalar(10),
                           blinding: random_blinding() };
        let o2 = Opening { id: hash_identity(b"b"), val: value_to_scalar(20),
                           blinding: random_blinding() };
        let sum = Opening {
            id: o1.id + o2.id,
            val: o1.val + o2.val,
            blinding: o1.blinding + o2.blinding,
        };
        assert_eq!(commit(&pp, &o1) + commit(&pp, &o2), commit(&pp, &sum));
    }
}