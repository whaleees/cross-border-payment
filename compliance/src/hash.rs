use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use ibc::commitment::Commitment;
use sha2::{Digest, Sha256};

const PREFIX: &[u8] = b"compliance/v1/";

// Every point of a list compressed. A round hashes the same lists into stmt, the
// state tokens and the shuffle transcript, and one compression costs about as much
// as twenty point additions, so each side compresses a list once and passes the bytes
// on (decision 34).
pub fn compress(cs: &[Commitment]) -> Vec<CompressedRistretto> {
    cs.iter().map(|c| c.0.compress()).collect()
}

// H(label, ...) = SHA-256("compliance/v1/" || label || 0x00 || parts), decision 25.
// Points, scalars, integers and 32-byte values have a fixed length; lists and free
// bytes carry their length first. So two different inputs never give the same bytes,
// and a hash under one label can never stand in for a hash under another.
#[derive(Clone)]
pub struct Fingerprint(Sha256);

impl Fingerprint {
    pub fn new(label: &[u8]) -> Self {
        let mut h = Sha256::new();
        h.update(PREFIX);
        h.update(label);
        h.update([0u8]);
        Fingerprint(h)
    }

    pub fn point(mut self, p: &RistrettoPoint) -> Self {
        self.0.update(p.compress().as_bytes());
        self
    }

    // A list of points, preceded by its length.
    pub fn points(self, ps: &[RistrettoPoint]) -> Self {
        ps.iter().fold(self.u32(ps.len() as u32), |h, p| h.point(p))
    }

    // A list of commitments, preceded by its length.
    pub fn commitments(self, cs: &[Commitment]) -> Self {
        cs.iter().fold(self.u32(cs.len() as u32), |h, c| h.point(&c.0))
    }

    // A list of points compressed earlier, preceded by its length: the same bytes as
    // `commitments` on the same points.
    pub fn compressed(self, ps: &[CompressedRistretto]) -> Self {
        ps.iter().fold(self.u32(ps.len() as u32), |h, p| h.fixed(p.as_bytes()))
    }

    pub fn scalar(mut self, s: &Scalar) -> Self {
        self.0.update(s.as_bytes());
        self
    }

    pub fn u32(mut self, x: u32) -> Self {
        self.0.update(x.to_le_bytes());
        self
    }

    pub fn u64(mut self, x: u64) -> Self {
        self.0.update(x.to_le_bytes());
        self
    }

    // A fixed 32-byte value: rho, cm, round_id, an earlier fingerprint, a point
    // compressed earlier.
    pub fn fixed(mut self, b: &[u8; 32]) -> Self {
        self.0.update(b);
        self
    }

    // Free-length bytes, preceded by their length.
    pub fn bytes(mut self, b: &[u8]) -> Self {
        self.0.update((b.len() as u64).to_le_bytes());
        self.0.update(b);
        self
    }

    pub fn finish(self) -> [u8; 32] {
        self.0.finalize().into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT as G;

    #[test]
    fn same_input_same_output() {
        let a = Fingerprint::new(b"cm").fixed(&[7; 32]).finish();
        let b = Fingerprint::new(b"cm").fixed(&[7; 32]).finish();
        assert_eq!(a, b);
    }

    #[test]
    fn the_label_separates_uses() {
        // cm = H("cm", rho) and nf = H("nf", rho) come from the same rho. If they
        // were equal, the verifier that signs cm would know nf in advance.
        let rho = [7u8; 32];
        assert_ne!(Fingerprint::new(b"cm").fixed(&rho).finish(), Fingerprint::new(b"nf").fixed(&rho).finish());
    }

    #[test]
    fn a_label_cannot_absorb_the_start_of_the_data() {
        // Without the 0x00 separator, label "ab" + data "c" and label "a" + data
        // "bc" would hash the same bytes.
        let x = Fingerprint::new(b"ab").bytes(b"c").finish();
        let y = Fingerprint::new(b"a").bytes(b"bc").finish();
        assert_ne!(x, y);
    }

    #[test]
    fn list_lengths_are_bound() {
        // ([P, 2P], [3P]) and ([P], [2P, 3P]) concatenate to the same points; the
        // length prefixes keep them apart.
        let (p1, p2, p3) = (G, G + G, G + G + G);
        let x = Fingerprint::new(b"stmt").points(&[p1, p2]).points(&[p3]).finish();
        let y = Fingerprint::new(b"stmt").points(&[p1]).points(&[p2, p3]).finish();
        assert_ne!(x, y);
    }

    #[test]
    fn compressed_points_hash_like_the_points() {
        // Decision 34 changes how often a point is compressed, not what is hashed.
        let cs: Vec<Commitment> = [G, G + G, G + G + G].map(Commitment).to_vec();
        let enc = compress(&cs);
        assert_eq!(Fingerprint::new(b"t").commitments(&cs).finish(), Fingerprint::new(b"t").compressed(&enc).finish());
        assert_eq!(Fingerprint::new(b"t").point(&G).finish(), Fingerprint::new(b"t").fixed(enc[0].as_bytes()).finish());
    }

    #[test]
    fn byte_lengths_are_bound() {
        let x = Fingerprint::new(b"t").bytes(b"ab").bytes(b"c").finish();
        let y = Fingerprint::new(b"t").bytes(b"a").bytes(b"bc").finish();
        assert_ne!(x, y);
    }

    #[test]
    fn every_part_changes_the_output() {
        let base = || Fingerprint::new(b"t");
        let full = |p: RistrettoPoint, s: u64, a: u32, f: u8| {
            base().point(&p).scalar(&Scalar::from(s)).u32(a).u64(s).fixed(&[f; 32]).finish()
        };
        let h = full(G, 5, 1, 9);
        assert_ne!(h, full(G + G, 5, 1, 9));
        assert_ne!(h, full(G, 6, 1, 9));
        assert_ne!(h, full(G, 5, 2, 9));
        assert_ne!(h, full(G, 5, 1, 8));
    }
}
