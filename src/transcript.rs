use curve25519_dalek::{RistrettoPoint, Scalar};
use merlin::Transcript;

use crate::params::PublicParams;

#[derive(Clone)]
pub struct Challenge(Transcript);

impl Challenge {
    // Start a transcript
    pub fn new(domain: &'static [u8], pp: &PublicParams) -> Self
    {
        let mut tr = Transcript::new(domain);
        tr.append_message(b"g_iden", pp.g_iden.compress().as_bytes());
        tr.append_message(b"g_val", pp.g_val.compress().as_bytes());
        tr.append_message(b"g_ran", pp.g_ran.compress().as_bytes());
        Challenge(tr)
    }

    pub fn point(mut self, label: &'static [u8], p: &RistrettoPoint) -> Self
    {
        self.0.append_message(label, p.compress().as_bytes());
        self
    }

    pub fn scalar(mut self, label: &'static [u8], s: &Scalar) -> Self
    {
        self.0.append_message(label, s.as_bytes());
        self
    }

    pub fn bytes(mut self, label: &'static [u8], b: &[u8]) -> Self
    {
        self.0.append_message(label, b);
        self
    }

    pub fn finish(mut self) -> Scalar
    {
        let mut buf = [0u8; 64];
        self.0.challenge_bytes(b"beta", &mut buf);
        Scalar::from_bytes_mod_order_wide(&buf)
    }

    pub fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar
    {
        let mut buf = [0u8; 64];
        self.0.challenge_bytes(label, &mut buf);
        Scalar::from_bytes_mod_order_wide(&buf)
    }
}