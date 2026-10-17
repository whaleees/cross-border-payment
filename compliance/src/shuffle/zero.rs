use curve25519_dalek::{RistrettoPoint, Scalar, traits::VartimeMultiscalarMul};
use ibc::commitment::random_blinding;

use super::{com_s, com_s_public, com_v, com_v_public};
use crate::params::ShuffleKey;

// S4, zero argument (Bayer-Groth full version 5.2). For committed rows a_1..a_m and
// b_0..b_{m-1}: sum_{i=1..m} phi_y(a_i, b_{i-1}) = 0.
// Lay out phi_y(a_i, b_j) for 0 <= i, j <= m (a_0 and b_m are fresh masks) and sum
// each diagonal i - j = k - m into d_k. Diagonal k = m + 1 is exactly the statement,
// so the verifier pins its commitment to 0 and lets one challenge e check them all.
//
// In code the m pairs are a[k], b[k] for k = 0..m-1: a[k] is a_{k+1}, b[k] is b_k.

// phi_y(u, w) = u_1*w_1*y + u_2*w_2*y^2 + ... + u_n*w_n*y^n
pub fn phi(y: Scalar, u: &[Scalar], w: &[Scalar]) -> Scalar {
    let mut y_pow = Scalar::ONE;
    u.iter()
        .zip(w)
        .map(|(ui, wi)| {
            y_pow *= y;
            ui * wi * y_pow
        })
        .sum()
}

// Sent before e.
#[derive(Clone, Debug)]
pub struct ZeroFirst {
    pub c_a0: RistrettoPoint,
    pub c_bm: RistrettoPoint,
    pub c_d: Vec<RistrettoPoint>, // c_D,k for k = 0..2m, skipping k = m + 1: 2m points
}

// Sent after e.
#[derive(Clone, Debug)]
pub struct ZeroResponse {
    pub a: Vec<Scalar>, // sum_i e^i * a_i
    pub b: Vec<Scalar>, // sum_j e^(m-j) * b_j
    pub r: Scalar,
    pub s: Scalar,
    pub t: Scalar,
}

pub struct ZeroState {
    a_full: Vec<Vec<Scalar>>, // a_0 (mask), a_1..a_m
    r_full: Vec<Scalar>,
    b_full: Vec<Vec<Scalar>>, // b_0..b_{m-1}, b_m (mask)
    s_full: Vec<Scalar>,
    t: Vec<Scalar>, // t_0..t_2m, with t_{m+1} = 0
}

impl ZeroFirst {
    pub fn size_bytes(&self) -> usize {
        32 * (2 + self.c_d.len())
    }
}

impl ZeroResponse {
    pub fn size_bytes(&self) -> usize {
        32 * (self.a.len() + self.b.len() + 3)
    }
}

fn powers(e: Scalar, count: usize) -> Vec<Scalar> {
    std::iter::successors(Some(Scalar::ONE), |p| Some(p * e)).take(count).collect()
}

// Steps 1-4. a, r: rows a_1..a_m and their blindings; b, s: rows b_0..b_{m-1}.
pub fn commit(key: &ShuffleKey, y: Scalar, a: &[Vec<Scalar>], r: &[Scalar], b: &[Vec<Scalar>], s: &[Scalar]) -> (ZeroFirst, ZeroState) {
    let m = a.len();
    assert!(m >= 1 && r.len() == m && b.len() == m && s.len() == m);
    let n = a[0].len();

    let a0: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
    let bm: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
    let (r0, sm) = (random_blinding(), random_blinding());
    let c_a0 = com_v(key, &a0, &r0);
    let c_bm = com_v(key, &bm, &sm);

    let a_full: Vec<Vec<Scalar>> = std::iter::once(a0).chain(a.iter().cloned()).collect();
    let b_full: Vec<Vec<Scalar>> = b.iter().cloned().chain(std::iter::once(bm)).collect();
    let r_full: Vec<Scalar> = std::iter::once(r0).chain(r.iter().copied()).collect();
    let s_full: Vec<Scalar> = s.iter().copied().chain(std::iter::once(sm)).collect();

    // d_k = sum of phi_y(a_i, b_j) over m + i - j = k. Scalar work only: (m+1)^2 * n.
    let mut d = vec![Scalar::ZERO; 2 * m + 1];
    for (i, ai) in a_full.iter().enumerate() {
        for (j, bj) in b_full.iter().enumerate() {
            d[m + i - j] += phi(y, ai, bj);
        }
    }

    let t: Vec<Scalar> = (0..=2 * m).map(|k| if k == m + 1 { Scalar::ZERO } else { random_blinding() }).collect();
    let c_d = (0..=2 * m).filter(|&k| k != m + 1).map(|k| com_s(key, &d[k], &t[k])).collect();

    (ZeroFirst { c_a0, c_bm, c_d }, ZeroState { a_full, r_full, b_full, s_full, t })
}

// Step 5.
pub fn respond(st: ZeroState, e: Scalar) -> ZeroResponse {
    let m = st.a_full.len() - 1;
    let n = st.a_full[0].len();
    let ep = powers(e, 2 * m + 1);

    let mut a = vec![Scalar::ZERO; n];
    for (i, ai) in st.a_full.iter().enumerate() {
        for (acc, x) in a.iter_mut().zip(ai) {
            *acc += ep[i] * x;
        }
    }
    let mut b = vec![Scalar::ZERO; n];
    for (j, bj) in st.b_full.iter().enumerate() {
        for (acc, x) in b.iter_mut().zip(bj) {
            *acc += ep[m - j] * x;
        }
    }
    ZeroResponse {
        a,
        b,
        r: st.r_full.iter().zip(&ep).map(|(r, w)| w * r).sum(),
        s: st.s_full.iter().enumerate().map(|(j, s)| ep[m - j] * s).sum(),
        t: st.t.iter().zip(&ep).map(|(t, w)| w * t).sum(),
    }
}

// Steps 6-9. c_a: commitments to a_1..a_m; c_b: to b_0..b_{m-1}; rows of n entries.
pub fn check(key: &ShuffleKey, n: usize, y: Scalar, c_a: &[RistrettoPoint], c_b: &[RistrettoPoint], first: &ZeroFirst, resp: &ZeroResponse, e: Scalar) -> bool {
    let m = c_a.len();
    if m == 0 || c_b.len() != m || first.c_d.len() != 2 * m || resp.a.len() != n || resp.b.len() != n || key.g.len() < n {
        return false;
    }
    let ep = powers(e, 2 * m + 1);

    // 7: sum_{i=0..m} e^i * c_{a,i} opens to a.
    let lhs_a = RistrettoPoint::vartime_multiscalar_mul(&ep[..=m], std::iter::once(&first.c_a0).chain(c_a));
    if lhs_a != com_v_public(key, &resp.a, &resp.r) {
        return false;
    }

    // 8: sum_{j=0..m} e^(m-j) * c_{b,j} opens to b.
    let lhs_b = RistrettoPoint::vartime_multiscalar_mul(
        (0..=m).map(|j| ep[m - j]),
        c_b.iter().chain(std::iter::once(&first.c_bm)),
    );
    if lhs_b != com_v_public(key, &resp.b, &resp.s) {
        return false;
    }

    // 6 and 9: c_D,{m+1} is the identity (a commitment to 0 with blinding 0), so it
    // drops out of the sum; the rest must open to phi_y(a, b) = sum_k e^k * d_k.
    // (Collected first: the MSM needs iterators of known, equal length.)
    let weights: Vec<Scalar> = (0..=2 * m).filter(|&k| k != m + 1).map(|k| ep[k]).collect();
    let lhs_d = RistrettoPoint::vartime_multiscalar_mul(&weights, &first.c_d);
    lhs_d == com_s_public(key, &phi(y, &resp.a, &resp.b), &resp.t)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ibc::params::PublicParams;

    struct Instance {
        a: Vec<Vec<Scalar>>,
        r: Vec<Scalar>,
        b: Vec<Vec<Scalar>>,
        s: Vec<Scalar>,
        c_a: Vec<RistrettoPoint>,
        c_b: Vec<RistrettoPoint>,
    }

    fn rows(m: usize, n: usize) -> Vec<Vec<Scalar>> {
        (0..m).map(|_| (0..n).map(|_| random_blinding()).collect()).collect()
    }

    // m random pairs, then a_1's first entry is solved so the whole sum is zero.
    fn instance(key: &ShuffleKey, m: usize, n: usize, y: Scalar, zero: bool) -> Instance {
        let mut a = rows(m, n);
        let b = rows(m, n);
        if zero {
            let rest: Scalar = (0..m).map(|k| phi(y, &a[k], &b[k])).sum::<Scalar>() - a[0][0] * b[0][0] * y;
            a[0][0] = -rest * (b[0][0] * y).invert();
            assert_eq!((0..m).map(|k| phi(y, &a[k], &b[k])).sum::<Scalar>(), Scalar::ZERO);
        }
        let r: Vec<Scalar> = (0..m).map(|_| random_blinding()).collect();
        let s: Vec<Scalar> = (0..m).map(|_| random_blinding()).collect();
        let c_a = a.iter().zip(&r).map(|(x, r)| com_v(key, x, r)).collect();
        let c_b = b.iter().zip(&s).map(|(x, s)| com_v(key, x, s)).collect();
        Instance { a, r, b, s, c_a, c_b }
    }

    fn prove(key: &ShuffleKey, y: Scalar, inst: &Instance, e: Scalar) -> (ZeroFirst, ZeroResponse) {
        let (first, st) = commit(key, y, &inst.a, &inst.r, &inst.b, &inst.s);
        (first, respond(st, e))
    }

    #[test]
    fn a_zero_sum_verifies() {
        for (m, n) in [(1, 3), (2, 2), (4, 5), (16, 8)] {
            let key = ShuffleKey::new(&PublicParams::setup(), n);
            let (y, e) = (random_blinding(), random_blinding());
            let inst = instance(&key, m, n, y, true);
            let (first, resp) = prove(&key, y, &inst, e);
            assert!(check(&key, n, y, &inst.c_a, &inst.c_b, &first, &resp, e), "m = {m}, n = {n}");
        }
    }

    #[test]
    fn a_non_zero_sum_fails() {
        // The honest prover's d_{m+1} is the non-zero sum, but the verifier pins
        // that diagonal to 0.
        let key = ShuffleKey::new(&PublicParams::setup(), 4);
        let (y, e) = (random_blinding(), random_blinding());
        let inst = instance(&key, 3, 4, y, false);
        let (first, resp) = prove(&key, y, &inst, e);
        assert!(!check(&key, 4, y, &inst.c_a, &inst.c_b, &first, &resp, e));
    }

    #[test]
    fn a_different_committed_row_fails() {
        let key = ShuffleKey::new(&PublicParams::setup(), 4);
        let (y, e) = (random_blinding(), random_blinding());
        let mut inst = instance(&key, 3, 4, y, true);
        let (first, resp) = prove(&key, y, &inst, e);
        inst.c_a[1] = com_v(&key, &rows(1, 4)[0], &inst.r[1]);
        assert!(!check(&key, 4, y, &inst.c_a, &inst.c_b, &first, &resp, e));
    }

    #[test]
    fn another_y_or_e_fails() {
        // y defines the statement; e the challenge. Both must be the ones used.
        let key = ShuffleKey::new(&PublicParams::setup(), 4);
        let (y, e) = (random_blinding(), random_blinding());
        let inst = instance(&key, 3, 4, y, true);
        let (first, resp) = prove(&key, y, &inst, e);
        assert!(!check(&key, 4, random_blinding(), &inst.c_a, &inst.c_b, &first, &resp, e));
        assert!(!check(&key, 4, y, &inst.c_a, &inst.c_b, &first, &resp, random_blinding()));
    }

    #[test]
    fn a_tampered_diagonal_commitment_fails() {
        let key = ShuffleKey::new(&PublicParams::setup(), 4);
        let (y, e) = (random_blinding(), random_blinding());
        let inst = instance(&key, 3, 4, y, true);
        let (mut first, resp) = prove(&key, y, &inst, e);
        first.c_d[0] += key.h;
        assert!(!check(&key, 4, y, &inst.c_a, &inst.c_b, &first, &resp, e));
    }

    #[test]
    fn wrong_lengths_are_rejected() {
        let key = ShuffleKey::new(&PublicParams::setup(), 4);
        let (y, e) = (random_blinding(), random_blinding());
        let inst = instance(&key, 3, 4, y, true);
        let (first, resp) = prove(&key, y, &inst, e);
        assert!(!check(&key, 4, y, &inst.c_a[..2], &inst.c_b, &first, &resp, e));
        let mut short = first.clone();
        short.c_d.pop();
        assert!(!check(&key, 4, y, &inst.c_a, &inst.c_b, &short, &resp, e));
    }

    #[test]
    fn sizes_are_2m_plus_2_points_and_2n_plus_3_scalars() {
        let key = ShuffleKey::new(&PublicParams::setup(), 63);
        let (y, e) = (random_blinding(), random_blinding());
        let inst = instance(&key, 16, 63, y, true);
        let (first, resp) = prove(&key, y, &inst, e);
        assert_eq!(first.size_bytes(), 32 * (2 * 16 + 2));
        assert_eq!(resp.size_bytes(), 32 * (2 * 63 + 3));
    }
}
