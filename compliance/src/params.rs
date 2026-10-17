use curve25519_dalek::ristretto::RistrettoPoint;
use ibc::params::PublicParams;

// Generator sets this crate adds on top of Kresna's pp. derive_generators labels
// them IBC/v1/gen/derived/<set>/<i> and checks they avoid g_iden, g_val, g_ran.
pub const SET_TAG: &[u8] = b"tag";
pub const SET_SHUFFLE_G: &[u8] = b"shuffle/g";
pub const SET_SHUFFLE_H: &[u8] = b"shuffle/h";

pub const PERIOD_DAYS: u32 = 365; // T, the same at every verifier (decision 18a)
pub const DATE_BITS: usize = 16; // range proof for theta - 1 - t: up to 65,535 days
pub const VALUE_BITS: usize = 64; // range proof for amounts, S and B - S, in SGD cents

// theta, the first day that still counts. The window is the last T days, today
// included: t_now - T + 1 ..= t_now (decision 32). A record expires when t <= theta - 1.
pub fn window_start(t_now: u32, period: u32) -> u32 {
    (t_now + 1).saturating_sub(period)
}

// pp plus the registration-tag generator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    pub pp: PublicParams,
    pub g_tag: RistrettoPoint, // tag = id * g_tag, no blinding (decision 14)
}

impl Params {
    pub fn setup() -> Self {
        let pp = PublicParams::setup();
        let g_tag = pp.derive_generators(SET_TAG, 1)[0];
        Params { pp, g_tag }
    }
}

// The shuffle's commitment key: comV(a; r) = sum a_l*g_l + r*h. It commits to rows of
// scalars (the permutation, x^pi), never to transactions, so it is separate from pp.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShuffleKey {
    pub g: Vec<RistrettoPoint>,
    pub h: RistrettoPoint,
}

impl ShuffleKey {
    // n message generators. A longer key extends a shorter one, so a key built for
    // the largest row length also serves every shorter row.
    pub fn new(pp: &PublicParams, n: usize) -> Self {
        ShuffleKey {
            g: pp.derive_generators(SET_SHUFFLE_G, n),
            h: pp.derive_generators(SET_SHUFFLE_H, 1)[0],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::traits::Identity;
    use sha2::Sha512;
    use std::collections::HashSet;

    #[test]
    fn the_window_holds_exactly_t_days() {
        // On 15 Oct 2026 (day 20,741) with T = 365, the window starts 16 Oct 2025.
        let theta = window_start(20_741, 365);
        assert_eq!(theta, 20_377);
        assert_eq!(20_741 - theta + 1, 365);
        assert_eq!(window_start(20_741, 30), 20_712);
    }

    #[test]
    fn setup_is_deterministic() {
        assert_eq!(Params::setup(), Params::setup());
    }

    #[test]
    fn g_tag_is_the_published_label_hashed_to_the_curve() {
        // Anyone can recompute g_tag from its label, so nobody chose it.
        let mut label = b"IBC/v1/gen/derived/tag/".to_vec();
        label.extend_from_slice(&0u32.to_le_bytes());
        let expected = RistrettoPoint::hash_from_bytes::<Sha512>(&label);
        assert_eq!(Params::setup().g_tag, expected);
    }

    #[test]
    fn every_generator_is_distinct_and_not_the_identity() {
        // derive_generators checks each set against pp, but not one set against
        // another. Check all of them together here.
        let params = Params::setup();
        let key = ShuffleKey::new(&params.pp, 64);
        let mut all = vec![params.pp.g_iden, params.pp.g_val, params.pp.g_ran, params.g_tag, key.h];
        all.extend(key.g.iter().copied());

        let mut seen = HashSet::new();
        for g in &all {
            assert_ne!(*g, RistrettoPoint::identity());
            assert!(seen.insert(g.compress().to_bytes()), "two generators coincide");
        }
    }

    #[test]
    fn a_longer_shuffle_key_extends_a_shorter_one() {
        let pp = PublicParams::setup();
        let short = ShuffleKey::new(&pp, 3);
        let long = ShuffleKey::new(&pp, 10);
        assert_eq!(long.g[..3], short.g[..]);
        assert_eq!(long.h, short.h);
    }
}
