// The shuffle argument (shuffle_argument.md): Bayer-Groth with an m x n grid.
// Each sub-argument comes in interactive pieces (commit / respond / check), like
// Kresna's vver.rs, because S4, S5 and S6 answer one shared challenge e: all their
// first messages go into the transcript before e is drawn.
pub mod svp;
pub mod zero;
pub mod hadamard;
pub mod product;
pub mod multiexp;
pub mod argument;

pub use argument::ShuffleProof;

use curve25519_dalek::RistrettoPoint;
use curve25519_dalek::Scalar;

use crate::params::ShuffleKey;

// Multi-scalar multiplication over the prover's secret scalars (the permutation,
// x^pi, masks). Constant-time by default (shuffle_argument.md, note 4). The
// vartime-prover feature swaps in the faster variable-time version, so the benchmark
// can show what constant time costs.
pub(crate) fn msm_secret(scalars: &[Scalar], points: &[RistrettoPoint]) -> RistrettoPoint {
    #[cfg(not(feature = "vartime-prover"))]
    {
        use curve25519_dalek::traits::MultiscalarMul;
        RistrettoPoint::multiscalar_mul(scalars, points)
    }
    #[cfg(feature = "vartime-prover")]
    {
        use curve25519_dalek::traits::VartimeMultiscalarMul;
        RistrettoPoint::vartime_multiscalar_mul(scalars, points)
    }
}

// comV(a; r) = sum a_l*g_l + r*h.
pub fn com_v(key: &ShuffleKey, a: &[Scalar], r: &Scalar) -> RistrettoPoint {
    assert!(a.len() <= key.g.len(), "shuffle key too short for this row");
    let scalars: Vec<Scalar> = a.iter().copied().chain([*r]).collect();
    let points: Vec<RistrettoPoint> = key.g[..a.len()].iter().copied().chain([key.h]).collect();
    msm_secret(&scalars, &points)
}

// The same commitments on the verifier's side, where every scalar is a public
// response: variable time is safe there, and faster (decision 33).
pub fn com_v_public(key: &ShuffleKey, a: &[Scalar], r: &Scalar) -> RistrettoPoint {
    use curve25519_dalek::traits::VartimeMultiscalarMul;
    assert!(a.len() <= key.g.len(), "shuffle key too short for this row");
    RistrettoPoint::vartime_multiscalar_mul(a.iter().chain([r]), key.g[..a.len()].iter().chain([&key.h]))
}

pub fn com_s_public(key: &ShuffleKey, a: &Scalar, t: &Scalar) -> RistrettoPoint {
    use curve25519_dalek::traits::VartimeMultiscalarMul;
    RistrettoPoint::vartime_multiscalar_mul([a, t], [&key.g[0], &key.h])
}

// comS(a; t) = a*g_1 + t*h, a commitment to one scalar.
pub fn com_s(key: &ShuffleKey, a: &Scalar, t: &Scalar) -> RistrettoPoint {
    a * key.g[0] + t * key.h
}

// m rows of n columns holding N >= N_real positions; positions past N_real are
// padding. Position j (0-based) sits in row j / n, column j % n.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Grid {
    pub m: usize,
    pub n: usize,
}

impl Grid {
    // m = min(16, floor(sqrt N)) (decision 29). With the floor, n = ceil(N/m) >= 2
    // for every N >= 2, which S5 needs.
    pub fn for_len(n_real: usize) -> Self {
        Self::with_rows(n_real, 16.min(n_real.isqrt()))
    }

    // A chosen m, for the experiments that sweep m (decision 18f: 1, 4, 16, 32).
    pub fn with_rows(n_real: usize, m: usize) -> Self {
        assert!(n_real >= 2, "a shuffle needs at least two pairs");
        assert!(m >= 1);
        let n = n_real.div_ceil(m);
        assert!(n >= 2, "rows of one column leave S5 nothing to multiply");
        Grid { m, n }
    }

    pub fn len(&self) -> usize {
        self.m * self.n
    }

    // Cut a vector of length m*n into its m rows.
    pub fn rows<T: Clone>(&self, v: &[T]) -> Vec<Vec<T>> {
        assert_eq!(v.len(), self.len());
        v.chunks(self.n).map(|r| r.to_vec()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ibc::commitment::random_blinding;
    use ibc::params::PublicParams;

    #[test]
    fn grid_shapes_follow_decision_29() {
        // (N, m, n): the floor keeps n >= 2 where the ceiling gave N = 2 a 2 x 1 grid.
        for (n_real, m, n) in [
            (2, 1, 2),
            (3, 1, 3),
            (4, 2, 2),
            (8, 2, 4),
            (9, 3, 3),
            (255, 15, 17),
            (256, 16, 16),
            (1_000, 16, 63),
            (10_000, 16, 625),
        ] {
            assert_eq!(Grid::for_len(n_real), Grid { m, n }, "N = {n_real}");
        }
    }

    #[test]
    fn every_grid_has_at_least_two_columns_and_room_for_everything() {
        for n_real in 2..=2_000 {
            let g = Grid::for_len(n_real);
            assert!(g.n >= 2, "N = {n_real}");
            assert!(g.len() >= n_real && g.len() - n_real < g.n, "N = {n_real}");
        }
    }

    #[test]
    fn experiment_grids_with_a_chosen_m() {
        assert_eq!(Grid::with_rows(10_000, 1), Grid { m: 1, n: 10_000 });
        assert_eq!(Grid::with_rows(10_000, 32), Grid { m: 32, n: 313 });
    }

    #[test]
    fn rows_cut_in_order() {
        let g = Grid { m: 2, n: 3 };
        assert_eq!(g.rows(&[1, 2, 3, 4, 5, 6]), vec![vec![1, 2, 3], vec![4, 5, 6]]);
    }

    #[test]
    fn commitments_are_homomorphic() {
        // The verifier builds comV(y*a + b - z; y*r + s) from comV(a; r) and
        // comV(b; s) alone (S1 step 14). That only works if comV adds up.
        let key = ShuffleKey::new(&PublicParams::setup(), 4);
        let a: Vec<Scalar> = (1..=4u64).map(Scalar::from).collect();
        let b: Vec<Scalar> = (0..4).map(|_| random_blinding()).collect();
        let (r, s, y) = (random_blinding(), random_blinding(), random_blinding());

        let combined: Vec<Scalar> = a.iter().zip(&b).map(|(ai, bi)| y * ai + bi).collect();
        assert_eq!(y * com_v(&key, &a, &r) + com_v(&key, &b, &s), com_v(&key, &combined, &(y * r + s)));
        assert_eq!(com_s(&key, &a[0], &r), com_v(&key, &a[..1], &r));
    }

    #[test]
    fn the_verifiers_variable_time_commitments_are_the_same_points() {
        // Decision 33 changes how fast the verifier computes, not what.
        let key = ShuffleKey::new(&PublicParams::setup(), 8);
        let a: Vec<Scalar> = (0..8).map(|_| random_blinding()).collect();
        let r = random_blinding();
        assert_eq!(com_v_public(&key, &a, &r), com_v(&key, &a, &r));
        assert_eq!(com_v_public(&key, &a[..3], &r), com_v(&key, &a[..3], &r));
        assert_eq!(com_s_public(&key, &a[0], &r), com_s(&key, &a[0], &r));
    }
}
