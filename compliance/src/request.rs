use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use ibc::commitment::Commitment;

use crate::hash::Fingerprint;

// x = (tid, v, t_now, T, B, round_id, kid): the verifier's request (G3 step 3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Request {
    pub tid: Commitment,
    pub v: u64,        // amount of this payment, SGD cents
    pub t_now: u32,    // UTC day number, from the verifier's clock
    pub period: u32,   // T
    pub limit: u64,    // B, SGD cents
    pub round_id: [u8; 32],
    pub kid: u32,      // the verifier's key number in the registry
}

impl Request {
    pub const LEN: usize = 32 + 8 + 4 + 4 + 8 + 32 + 4;

    // enc(x): fixed-length, 92 bytes.
    pub fn to_bytes(&self) -> [u8; Self::LEN] {
        let mut out = [0u8; Self::LEN];
        out[0..32].copy_from_slice(&self.tid.to_bytes());
        out[32..40].copy_from_slice(&self.v.to_le_bytes());
        out[40..44].copy_from_slice(&self.t_now.to_le_bytes());
        out[44..48].copy_from_slice(&self.period.to_le_bytes());
        out[48..56].copy_from_slice(&self.limit.to_le_bytes());
        out[56..88].copy_from_slice(&self.round_id);
        out[88..92].copy_from_slice(&self.kid.to_le_bytes());
        out
    }

    // H("request", enc(x)). Signed under the same key as state tokens; the label
    // keeps a request signature from passing as a token signature (decision 23).
    pub fn digest(&self) -> [u8; 32] {
        Fingerprint::new(b"request").bytes(&self.to_bytes()).finish()
    }

    // G3 step 4.
    pub fn sign(self, sk: &SigningKey) -> SignedRequest {
        SignedRequest { x: self, sig: sk.sign(&self.digest()) }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignedRequest {
    pub x: Request,
    pub sig: Signature,
}

impl SignedRequest {
    // G3 step 6.
    pub fn verify(&self, pk: &VerifyingKey) -> bool {
        pk.verify_strict(&self.x.digest(), &self.sig).is_ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state_token::state_hash;
    use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT as G;
    use rand_core::OsRng;

    fn request() -> Request {
        Request { tid: Commitment(G), v: 3_200, t_now: 20_741, period: 365, limit: 500_000, round_id: [7; 32], kid: 1 }
    }

    #[test]
    fn a_signed_request_verifies_under_its_key_only() {
        let sk = SigningKey::generate(&mut OsRng);
        let signed = request().sign(&sk);
        assert!(signed.verify(&sk.verifying_key()));
        assert!(!signed.verify(&SigningKey::generate(&mut OsRng).verifying_key()));
    }

    #[test]
    fn every_field_is_signed() {
        let sk = SigningKey::generate(&mut OsRng);
        let signed = request().sign(&sk);
        let base = request();
        for changed in [
            Request { tid: Commitment(G + G), ..base },
            Request { v: 3_201, ..base },
            Request { t_now: 20_742, ..base },
            Request { period: 366, ..base },
            Request { limit: 1_000, ..base },
            Request { round_id: [8; 32], ..base },
            Request { kid: 2, ..base },
        ] {
            assert!(!SignedRequest { x: changed, ..signed }.verify(&sk.verifying_key()));
        }
    }

    #[test]
    fn a_request_signature_is_not_a_state_token_signature() {
        // Same key, different labels: the two signed messages can never coincide.
        assert_ne!(request().digest(), state_hash(&[], &[], &[0; 32]));
        assert_eq!(request().to_bytes().len(), 92);
    }
}
