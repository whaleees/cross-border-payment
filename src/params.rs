use std::collections::HashSet;

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;
use sha2::{Digest, Sha512};

pub const LABEL_G_IDEN: &[u8] = b"IBC/v1/gen/iden";
pub const LABEL_G_VAL: &[u8] = b"IBC/v1/gen/val";
pub const LABEL_G_RAN: &[u8] = b"IBC/v1/gen/ran";
pub const LABEL_ID_HASH: &[u8] = b"IBC/v1/id-to-scalar";
pub const LABEL_DERIVED: &[u8] = b"IBC/v1/gen/derived/";

// Public parameters
// 3 independent generators
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicParams {
    pub g_iden: RistrettoPoint, // carries identity
    pub g_val: RistrettoPoint,  // carries val
    pub g_ran: RistrettoPoint,  // carries blinding
}

impl PublicParams {
    pub fn setup() -> Self {
        // Using public group elements on 3 generators
        let g_iden = RistrettoPoint::hash_from_bytes::<Sha512>(LABEL_G_IDEN);
        let g_val = RistrettoPoint::hash_from_bytes::<Sha512>(LABEL_G_VAL);
        let g_ran = RistrettoPoint::hash_from_bytes::<Sha512>(LABEL_G_RAN);

        let id_elem = RistrettoPoint::identity();
        assert!(g_iden != id_elem, "g_iden is the identity element");
        assert!(g_val  != id_elem, "g_val is the identity element");
        assert!(g_ran  != id_elem, "g_ran is the identity element");
        assert!(g_iden != g_val,   "g_iden and g_val coincide");
        assert!(g_val  != g_ran,   "g_val and g_ran coincide");
        assert!(g_iden != g_ran,   "g_iden and g_ran coincide");

        PublicParams { g_iden, g_val, g_ran }
    }

    pub fn to_bytes(&self) -> [[u8; 32]; 3] {
        [
            self.g_iden.compress().to_bytes(),
            self.g_val.compress().to_bytes(),
            self.g_ran.compress().to_bytes(),
        ]
    }

    // n more generators for a protocol that shares pp (e.g. a commitment key).
    // Same hash-to-group as Setup, one label per generator:
    //   LABEL_DERIVED || set || "/" || i (u32, little-endian)
    // so no one knows a discrete-log relation between these and g_iden, g_val, g_ran.
    pub fn derive_generators(&self, set: &[u8], n: usize) -> Vec<RistrettoPoint> {
        let gens: Vec<RistrettoPoint> = (0..n as u32)
            .map(|i| {
                let mut label = LABEL_DERIVED.to_vec();
                label.extend_from_slice(set);
                label.push(b'/');
                label.extend_from_slice(&i.to_le_bytes());
                RistrettoPoint::hash_from_bytes::<Sha512>(&label)
            })
            .collect();

        // Setup's step-3 abort, extended to the new generators.
        let mut seen: HashSet<[u8; 32]> = self.to_bytes().into_iter().collect();
        for g in &gens {
            assert!(*g != RistrettoPoint::identity(), "derived generator is the identity element");
            assert!(seen.insert(g.compress().to_bytes()), "derived generator coincides with another");
        }
        gens
    }
}

// Map a raw identity into a scalar
pub fn hash_identity(identity: &[u8]) -> Scalar {
    let mut hasher = Sha512::new();
    hasher.update(LABEL_ID_HASH);
    hasher.update(identity);
    Scalar::from_hash(hasher)
}

// Map a transaction amount into a scalar
pub fn value_to_scalar(value: u64) -> Scalar {
    Scalar::from(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn setup_is_deterministic() {
        assert_eq!(PublicParams::setup(), PublicParams::setup());
    }

    #[test]
    fn generators_are_distinct_and_non_identity() {
        let pp = PublicParams::setup();
        let id_elem = RistrettoPoint::identity();
        assert_ne!(pp.g_iden, id_elem);
        assert_ne!(pp.g_val,  id_elem);
        assert_ne!(pp.g_ran,  id_elem);
        assert_ne!(pp.g_iden, pp.g_val);
        assert_ne!(pp.g_val,  pp.g_ran);
        assert_ne!(pp.g_iden, pp.g_ran);
    }

    #[test]
    fn print_generator_test_vectors() {
        // cargo test -- --nocapture print_generator_test_vectors
        let pp = PublicParams::setup();
        for (name, bytes) in [("g_iden", pp.to_bytes()[0]),
                              ("g_val",  pp.to_bytes()[1]),
                              ("g_ran",  pp.to_bytes()[2])] {
            let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
            println!("{name} = {hex}");
        }
    }

    #[test]
    fn generators_match_published_test_vectors() {
        let hex = |b: [u8; 32]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        let [iden, val, ran] = PublicParams::setup().to_bytes();
        assert_eq!(hex(iden), "d47874bc8ca4f558116fa93fbb51474c6c39d165f423f7b54625e5b071321201");
        assert_eq!(hex(val),  "daabecbf093fc1ec0e2b40f600b84736df9519276cb431697652bc872c9e525f");
        assert_eq!(hex(ran),  "7a2cd623b6bdf05f52998960fe69d6d94d860cdc519e9a857ed725fa49116a73");
    }

    #[test]
    fn derived_generators_are_deterministic() {
        let pp = PublicParams::setup();
        assert_eq!(pp.derive_generators(b"ck", 8), pp.derive_generators(b"ck", 8));
    }

    #[test]
    fn derived_generators_depend_on_set_and_index() {
        let pp = PublicParams::setup();
        let a = pp.derive_generators(b"ck", 2);
        let b = pp.derive_generators(b"range", 2);
        assert_ne!(a[0], a[1]);
        assert_ne!(a[0], b[0]);
        // A longer set is the shorter one extended, not a different one.
        assert_eq!(pp.derive_generators(b"ck", 5)[..2], a[..]);
    }

    #[test]
    fn derived_generators_avoid_pp() {
        let pp = PublicParams::setup();
        for g in pp.derive_generators(b"ck", 64) {
            assert!(g != pp.g_iden && g != pp.g_val && g != pp.g_ran);
        }
    }

    #[test]
    fn identity_hash_separates_inputs() {
        assert_eq!(hash_identity(b"user_42"), hash_identity(b"user_42"));
        assert_ne!(hash_identity(b"user_42"), hash_identity(b"user_43"));
    }
}
