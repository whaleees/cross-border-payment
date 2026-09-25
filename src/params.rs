use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;
use sha2::{Digest, Sha512};

pub const LABEL_G_IDEN: &[u8] = b"IBC/v1/gen/iden";
pub const LABEL_G_VAL: &[u8] = b"IBC/v1/gen/val";
pub const LABEL_G_RAN: &[u8] = b"IBC/v1/gen/ran";
pub const LABEL_ID_HASH: &[u8] = b"IBC/v1/id-to-scalar";

// Public parameters
// 3 independent generators
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicParams {
    pub g_iden: RistrettoPoint, // carries identity
    pub g_val: RistrettoPoint,  // carries val
    pub g_ran: RistrettoPoint,  // carries blinding
    bytes: [[u8; 32]; 3],       // the three compressed once, for every transcript
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

        let bytes = [
            g_iden.compress().to_bytes(),
            g_val.compress().to_bytes(),
            g_ran.compress().to_bytes(),
        ];
        PublicParams { g_iden, g_val, g_ran, bytes }
    }

    pub fn to_bytes(&self) -> [[u8; 32]; 3] {
        self.bytes
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
    fn generators_match_the_test_vectors() {
        let hex = |b: [u8; 32]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        let pp = PublicParams::setup();
        let [g_iden, g_val, g_ran] = pp.to_bytes();
        assert_eq!(hex(g_iden), "d47874bc8ca4f558116fa93fbb51474c6c39d165f423f7b54625e5b071321201");
        assert_eq!(hex(g_val), "daabecbf093fc1ec0e2b40f600b84736df9519276cb431697652bc872c9e525f");
        assert_eq!(hex(g_ran), "7a2cd623b6bdf05f52998960fe69d6d94d860cdc519e9a857ed725fa49116a73");
        assert_eq!(g_iden, pp.g_iden.compress().to_bytes());
        assert_eq!(g_val, pp.g_val.compress().to_bytes());
        assert_eq!(g_ran, pp.g_ran.compress().to_bytes());
    }

    #[test]
    fn identity_hash_separates_inputs() {
        assert_eq!(hash_identity(b"user_42"), hash_identity(b"user_42"));
        assert_ne!(hash_identity(b"user_42"), hash_identity(b"user_43"));
    }
}
