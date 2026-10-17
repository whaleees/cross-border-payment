use curve25519_dalek::{RistrettoPoint, Scalar, traits::VartimeMultiscalarMul};
use ibc::commitment::random_blinding;

use super::com_v;
use super::zero::{self, ZeroFirst, ZeroResponse, ZeroState};
use crate::params::ShuffleKey;

// S3, Hadamard product argument (Bayer-Groth full version 5.1), m >= 2: c_P commits
// to w_1 o w_2 o ... o w_m, the entrywise product of the committed rows.
// The prover commits to the running products q_i = w_1 o ... o w_i. Each step
// q_{i+1} = w_{i+1} o q_i is one equation per column; weighting step i by x_h^i and
// column l by y_h^l folds all of them into one sum that must be zero, which S4 proves.
//
// Rows are 0-indexed here: w[0..m], q[0] = w[0], q[m-1] = P.

pub struct HadamardState {
    w: Vec<Vec<Scalar>>,
    u: Vec<Scalar>,
    q: Vec<Vec<Scalar>>,
    o: Vec<Scalar>, // blinding of each q[i]: o[0] = u[0], o[m-1] = u_P
}

// Steps 1-3. p and u_p open c_P; an honest prover passes the real entrywise product.
// Returns the commitments to the middle running products q[1..m-1].
pub fn commit(key: &ShuffleKey, w: &[Vec<Scalar>], u: &[Scalar], p: &[Scalar], u_p: Scalar) -> (Vec<RistrettoPoint>, HadamardState) {
    let m = w.len();
    assert!(m >= 2 && u.len() == m, "S3 needs m >= 2 rows");

    let mut q = vec![w[0].clone()];
    for row in &w[1..m - 1] {
        let next = q.last().unwrap().iter().zip(row).map(|(a, b)| a * b).collect();
        q.push(next);
    }
    q.push(p.to_vec()); // the claimed product; the zero argument checks this last step too

    let mut o: Vec<Scalar> = (0..m).map(|_| random_blinding()).collect();
    o[0] = u[0];
    o[m - 1] = u_p;

    let c_q_mid = (1..m - 1).map(|i| com_v(key, &q[i], &o[i])).collect();
    (c_q_mid, HadamardState { w: w.to_vec(), u: u.to_vec(), q, o })
}

fn powers(x: Scalar, count: usize) -> Vec<Scalar> {
    std::iter::successors(Some(Scalar::ONE), |p| Some(p * x)).take(count).collect()
}

// Steps 4-6, prover side: the zero-argument rows, then S4's first message.
//   pair k < m-1:  a = w[k+1],   b = x_h^(k+1) * q[k]
//   pair m-1:      a = (-1..-1), b = sum_{i=1..m-1} x_h^i * q[i]
pub fn commit_zero(st: HadamardState, key: &ShuffleKey, x_h: Scalar, y_h: Scalar) -> (ZeroFirst, ZeroState) {
    let m = st.w.len();
    let n = st.w[0].len();
    let xp = powers(x_h, m);

    let mut a: Vec<Vec<Scalar>> = st.w[1..].to_vec();
    let mut r: Vec<Scalar> = st.u[1..].to_vec();
    a.push(vec![-Scalar::ONE; n]);
    r.push(Scalar::ZERO);

    let mut b: Vec<Vec<Scalar>> = (0..m - 1).map(|k| st.q[k].iter().map(|v| xp[k + 1] * v).collect()).collect();
    let mut s: Vec<Scalar> = (0..m - 1).map(|k| xp[k + 1] * st.o[k]).collect();
    let mut b_last = vec![Scalar::ZERO; n];
    for i in 1..m {
        for (acc, v) in b_last.iter_mut().zip(&st.q[i]) {
            *acc += xp[i] * v;
        }
    }
    b.push(b_last);
    s.push((1..m).map(|i| xp[i] * st.o[i]).sum());

    zero::commit(key, y_h, &a, &r, &b, &s)
}

// The same rows' commitments, built by the verifier from c_w, the middle c_Q and c_P.
fn zero_commitments(key: &ShuffleKey, n: usize, c_w: &[RistrettoPoint], c_q_mid: &[RistrettoPoint], c_p: &RistrettoPoint, x_h: Scalar) -> (Vec<RistrettoPoint>, Vec<RistrettoPoint>) {
    let m = c_w.len();
    let xp = powers(x_h, m);
    let c_q: Vec<RistrettoPoint> = std::iter::once(c_w[0]).chain(c_q_mid.iter().copied()).chain([*c_p]).collect();

    let minus_one: RistrettoPoint = -key.g[..n].iter().sum::<RistrettoPoint>(); // comV(-1..-1; 0)
    let c_a: Vec<RistrettoPoint> = c_w[1..].iter().copied().chain([minus_one]).collect();

    let mut c_b: Vec<RistrettoPoint> = (0..m - 1).map(|k| xp[k + 1] * c_q[k]).collect();
    c_b.push(RistrettoPoint::vartime_multiscalar_mul(&xp[1..m], &c_q[1..m]));
    (c_a, c_b)
}

// Verifier: c_P is the entrywise product of the rows inside c_w.
#[allow(clippy::too_many_arguments)]
pub fn check(
    key: &ShuffleKey,
    n: usize,
    c_w: &[RistrettoPoint],
    c_p: &RistrettoPoint,
    c_q_mid: &[RistrettoPoint],
    x_h: Scalar,
    y_h: Scalar,
    zf: &ZeroFirst,
    zr: &ZeroResponse,
    e: Scalar,
) -> bool {
    let m = c_w.len();
    if m < 2 || c_q_mid.len() != m - 2 || key.g.len() < n {
        return false;
    }
    let (c_a, c_b) = zero_commitments(key, n, c_w, c_q_mid, c_p, x_h);
    zero::check(key, n, y_h, &c_a, &c_b, zf, zr, e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ibc::params::PublicParams;

    fn entrywise(rows: &[Vec<Scalar>]) -> Vec<Scalar> {
        rows[1..].iter().fold(rows[0].clone(), |acc, r| acc.iter().zip(r).map(|(a, b)| a * b).collect())
    }

    fn random_rows(m: usize, n: usize) -> Vec<Vec<Scalar>> {
        (0..m).map(|_| (0..n).map(|_| random_blinding()).collect()).collect()
    }

    // Prove "c_P = entrywise product of the rows" with the given claimed p, then check.
    fn run(m: usize, n: usize, p_claim: Option<Vec<Scalar>>) -> bool {
        let key = ShuffleKey::new(&PublicParams::setup(), n);
        let w = random_rows(m, n);
        let u: Vec<Scalar> = (0..m).map(|_| random_blinding()).collect();
        let c_w: Vec<RistrettoPoint> = w.iter().zip(&u).map(|(r, u)| com_v(&key, r, u)).collect();
        let p = p_claim.unwrap_or_else(|| entrywise(&w));
        let u_p = random_blinding();
        let c_p = com_v(&key, &p, &u_p);

        let (c_q_mid, st) = commit(&key, &w, &u, &p, u_p);
        let (x_h, y_h, e) = (random_blinding(), random_blinding(), random_blinding());
        let (zf, zs) = commit_zero(st, &key, x_h, y_h);
        let zr = zero::respond(zs, e);
        check(&key, n, &c_w, &c_p, &c_q_mid, x_h, y_h, &zf, &zr, e)
    }

    #[test]
    fn the_entrywise_product_verifies() {
        for (m, n) in [(2, 3), (3, 2), (5, 4), (16, 8)] {
            assert!(run(m, n, None), "m = {m}, n = {n}");
        }
    }

    #[test]
    fn a_c_p_that_is_not_the_entrywise_product_fails() {
        for (m, n) in [(2, 3), (5, 4)] {
            let fake: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
            assert!(!run(m, n, Some(fake)), "m = {m}, n = {n}");
        }
    }

    #[test]
    fn swapping_a_row_commitment_fails() {
        let (m, n) = (4, 3);
        let key = ShuffleKey::new(&PublicParams::setup(), n);
        let w = random_rows(m, n);
        let u: Vec<Scalar> = (0..m).map(|_| random_blinding()).collect();
        let mut c_w: Vec<RistrettoPoint> = w.iter().zip(&u).map(|(r, u)| com_v(&key, r, u)).collect();
        let p = entrywise(&w);
        let u_p = random_blinding();
        let c_p = com_v(&key, &p, &u_p);
        let (c_q_mid, st) = commit(&key, &w, &u, &p, u_p);
        let (x_h, y_h, e) = (random_blinding(), random_blinding(), random_blinding());
        let (zf, zs) = commit_zero(st, &key, x_h, y_h);
        let zr = zero::respond(zs, e);

        c_w[2] = com_v(&key, &random_rows(1, n)[0], &u[2]);
        assert!(!check(&key, n, &c_w, &c_p, &c_q_mid, x_h, y_h, &zf, &zr, e));
    }

    #[test]
    fn another_x_h_fails_and_a_wrong_middle_count_is_rejected() {
        let (m, n) = (4, 3);
        let key = ShuffleKey::new(&PublicParams::setup(), n);
        let w = random_rows(m, n);
        let u: Vec<Scalar> = (0..m).map(|_| random_blinding()).collect();
        let c_w: Vec<RistrettoPoint> = w.iter().zip(&u).map(|(r, u)| com_v(&key, r, u)).collect();
        let p = entrywise(&w);
        let u_p = random_blinding();
        let c_p = com_v(&key, &p, &u_p);
        let (c_q_mid, st) = commit(&key, &w, &u, &p, u_p);
        let (x_h, y_h, e) = (random_blinding(), random_blinding(), random_blinding());
        let (zf, zs) = commit_zero(st, &key, x_h, y_h);
        let zr = zero::respond(zs, e);

        assert!(check(&key, n, &c_w, &c_p, &c_q_mid, x_h, y_h, &zf, &zr, e));
        assert!(!check(&key, n, &c_w, &c_p, &c_q_mid, random_blinding(), y_h, &zf, &zr, e));
        assert!(!check(&key, n, &c_w, &c_p, &c_q_mid[..1], x_h, y_h, &zf, &zr, e));
    }
}
