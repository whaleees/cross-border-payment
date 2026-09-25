use curve25519_dalek::{RistrettoPoint, Scalar, ristretto::CompressedRistretto};

pub fn encode(points: &[RistrettoPoint], scalars: &[Scalar]) -> Vec<u8> {
    let mut out = Vec::with_capacity(32 * (points.len() + scalars.len()));
    for p in points {
        out.extend_from_slice(p.compress().as_bytes());
    }
    for s in scalars {
        out.extend_from_slice(s.as_bytes());
    }
    out
}

pub fn decode(
    bytes: &[u8],
    n_points: usize,
    n_scalars: usize,
) -> Option<(Vec<RistrettoPoint>, Vec<Scalar>)> {
    if bytes.len() != 32 * (n_points + n_scalars) {
        return None;
    }
    let (point_bytes, scalar_bytes) = bytes.split_at(32 * n_points);
    let points = point_bytes
        .chunks_exact(32)
        .map(|c| CompressedRistretto::from_slice(c).ok()?.decompress())
        .collect::<Option<Vec<_>>>()?;
    let scalars = scalar_bytes
        .chunks_exact(32)
        .map(|c| Option::from(Scalar::from_canonical_bytes(c.try_into().ok()?)))
        .collect::<Option<Vec<_>>>()?;
    Some((points, scalars))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand_core::OsRng;

    #[test]
    fn roundtrip() {
        let points = vec![RistrettoPoint::random(&mut OsRng), RistrettoPoint::random(&mut OsRng)];
        let scalars: Vec<Scalar> = (0..3).map(|_| Scalar::random(&mut OsRng)).collect();
        let bytes = encode(&points, &scalars);
        assert_eq!(bytes.len(), 32 * 5);
        assert_eq!(decode(&bytes, 2, 3), Some((points, scalars)));
    }

    #[test]
    fn wrong_length_is_rejected() {
        let bytes = encode(&[RistrettoPoint::random(&mut OsRng)], &[Scalar::ONE]);
        assert!(decode(&bytes, 1, 2).is_none());
        assert!(decode(&bytes[..63], 1, 1).is_none());
        assert!(decode(&[bytes.as_slice(), &[0]].concat(), 1, 1).is_none());
    }

    #[test]
    fn invalid_point_is_rejected() {
        // 0xff..ff is not a canonical field element; 1 is canonical but "negative",
        // which Ristretto never outputs. Neither encodes any point.
        let mut one = [0u8; 32];
        one[0] = 1;
        for bad in [[0xffu8; 32], one] {
            let bytes = [bad.as_slice(), Scalar::ONE.as_bytes().as_slice()].concat();
            assert!(decode(&bytes, 1, 1).is_none());
        }
    }

    #[test]
    fn non_canonical_scalar_is_rejected() {
        // p (the group order) reduces to 0: the same value as zero, written
        // differently. Accepting it would give every proof a second encoding.
        const P: [u8; 32] = [
            0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
            0xde, 0x14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
        ];
        assert_eq!(Scalar::from_bytes_mod_order(P), Scalar::ZERO);

        let t = RistrettoPoint::random(&mut OsRng).compress().to_bytes();
        assert!(decode(&[t.as_slice(), P.as_slice()].concat(), 1, 1).is_none());
        assert!(decode(&[t.as_slice(), Scalar::ZERO.as_bytes().as_slice()].concat(), 1, 1).is_some());
    }
}
