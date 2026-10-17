use curve25519_dalek::{RistrettoPoint, Scalar};
use ibc::commitment::random_blinding;

use super::com_v;
use super::hadamard::{self, HadamardState};
use super::svp::{self, SvpFirst, SvpResponse, SvpState};
use super::zero::{self, ZeroFirst, ZeroResponse, ZeroState};
use crate::params::ShuffleKey;

// S2, product argument (Bayer-Groth section 5): the product of every entry of the
// committed rows w_1..w_m is beta.
//   m = 1:   S5 on the single row.
//   m >= 2:  P = w_1 o ... o w_m (column products), committed in c_P;
//            S3 proves c_P is that entrywise product, S5 proves prod(P) = beta.
// Three prover phases, matching the moves of shuffle_argument.md section 2:
//   commit        -> ProductFirst   (move 5)
//   commit_second -> ProductSecond  (move 7, after x_h and y_h)
//   respond       -> ProductResponse (move 9, after e)

#[derive(Clone, Debug)]
pub struct ProductFirst {
    pub c_p: Option<RistrettoPoint>,  // None when m = 1
    pub c_q_mid: Vec<RistrettoPoint>, // S3's middle running products, m - 2 of them
}

#[derive(Clone, Debug)]
pub struct ProductSecond {
    pub zero: Option<ZeroFirst>, // S3's zero argument, None when m = 1
    pub svp: SvpFirst,
}

#[derive(Clone, Debug)]
pub struct ProductResponse {
    pub zero: Option<ZeroResponse>,
    pub svp: SvpResponse,
}

pub struct ProductState {
    hadamard: Option<HadamardState>,
    last: Vec<Scalar>, // the row S5 runs on: w_1 when m = 1, else P
    last_blinding: Scalar,
}

pub struct ProductState2 {
    zero: Option<ZeroState>,
    svp: SvpState,
}

impl ProductFirst {
    pub fn size_bytes(&self) -> usize {
        32 * (self.c_p.iter().count() + self.c_q_mid.len())
    }
}

impl ProductSecond {
    pub fn size_bytes(&self) -> usize {
        self.zero.as_ref().map_or(0, |z| z.size_bytes()) + 32 * 3
    }
}

impl ProductResponse {
    pub fn size_bytes(&self) -> usize {
        self.zero.as_ref().map_or(0, |z| z.size_bytes()) + self.svp.size_bytes()
    }
}

fn entrywise(w: &[Vec<Scalar>]) -> Vec<Scalar> {
    w[1..].iter().fold(w[0].clone(), |acc, r| acc.iter().zip(r).map(|(a, b)| a * b).collect())
}

// Steps 1-3 and S3's first move. w: the m rows, u: their blindings.
pub fn commit(key: &ShuffleKey, w: &[Vec<Scalar>], u: &[Scalar]) -> (ProductFirst, ProductState) {
    if w.len() == 1 {
        return commit_with_column_products(key, w, u, None);
    }
    commit_with_column_products(key, w, u, Some(entrywise(w)))
}

// Split out so a test can hand in column products that are not the real ones.
fn commit_with_column_products(key: &ShuffleKey, w: &[Vec<Scalar>], u: &[Scalar], p: Option<Vec<Scalar>>) -> (ProductFirst, ProductState) {
    assert!(!w.is_empty() && u.len() == w.len());
    match p {
        None => (
            ProductFirst { c_p: None, c_q_mid: Vec::new() },
            ProductState { hadamard: None, last: w[0].clone(), last_blinding: u[0] },
        ),
        Some(p) => {
            let u_p = random_blinding();
            let c_p = com_v(key, &p, &u_p);
            let (c_q_mid, h) = hadamard::commit(key, w, u, &p, u_p);
            (
                ProductFirst { c_p: Some(c_p), c_q_mid },
                ProductState { hadamard: Some(h), last: p, last_blinding: u_p },
            )
        }
    }
}

// Move 7: S3's zero argument (needs x_h, y_h) and S5's first message.
pub fn commit_second(st: ProductState, key: &ShuffleKey, x_h: Scalar, y_h: Scalar) -> (ProductSecond, ProductState2) {
    let (zero_first, zero_state) = match st.hadamard {
        Some(h) => {
            let (f, s) = hadamard::commit_zero(h, key, x_h, y_h);
            (Some(f), Some(s))
        }
        None => (None, None),
    };
    let (svp_first, svp_state) = svp::commit(key, &st.last, st.last_blinding);
    (ProductSecond { zero: zero_first, svp: svp_first }, ProductState2 { zero: zero_state, svp: svp_state })
}

// Move 9.
pub fn respond(st: ProductState2, e: Scalar) -> ProductResponse {
    ProductResponse { zero: st.zero.map(|z| zero::respond(z, e)), svp: svp::respond(st.svp, e) }
}

// Verifier: the product of every entry in the rows committed in c_w is beta.
#[allow(clippy::too_many_arguments)]
pub fn check(
    key: &ShuffleKey,
    n: usize,
    c_w: &[RistrettoPoint],
    beta: Scalar,
    first: &ProductFirst,
    x_h: Scalar,
    y_h: Scalar,
    second: &ProductSecond,
    resp: &ProductResponse,
    e: Scalar,
) -> bool {
    match (c_w.len(), &first.c_p, &second.zero, &resp.zero) {
        (0, ..) => false,
        (1, None, None, None) => first.c_q_mid.is_empty() && svp::check(key, n, &c_w[0], beta, &second.svp, &resp.svp, e),
        (m, Some(c_p), Some(zf), Some(zr)) if m >= 2 => {
            hadamard::check(key, n, c_w, c_p, &first.c_q_mid, x_h, y_h, zf, zr, e)
                && svp::check(key, n, c_p, beta, &second.svp, &resp.svp, e)
        }
        _ => false, // the shape of the proof does not match m
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ibc::params::PublicParams;

    fn scalars(rows: &[&[u64]]) -> Vec<Vec<Scalar>> {
        rows.iter().map(|r| r.iter().map(|&x| Scalar::from(x)).collect()).collect()
    }

    struct Run {
        key: ShuffleKey,
        n: usize,
        c_w: Vec<RistrettoPoint>,
        first: ProductFirst,
        second: ProductSecond,
        resp: ProductResponse,
        x_h: Scalar,
        y_h: Scalar,
        e: Scalar,
    }

    fn prove(w: Vec<Vec<Scalar>>, p: Option<Option<Vec<Scalar>>>) -> Run {
        let n = w[0].len();
        let key = ShuffleKey::new(&PublicParams::setup(), n);
        let u: Vec<Scalar> = w.iter().map(|_| random_blinding()).collect();
        let c_w = w.iter().zip(&u).map(|(r, u)| com_v(&key, r, u)).collect();
        let (first, st) = match p {
            None => commit(&key, &w, &u),
            Some(p) => commit_with_column_products(&key, &w, &u, p),
        };
        let (x_h, y_h, e) = (random_blinding(), random_blinding(), random_blinding());
        let (second, st2) = commit_second(st, &key, x_h, y_h);
        let resp = respond(st2, e);
        Run { key, n, c_w, first, second, resp, x_h, y_h, e }
    }

    fn holds(r: &Run, beta: u64) -> bool {
        check(&r.key, r.n, &r.c_w, Scalar::from(beta), &r.first, r.x_h, r.y_h, &r.second, &r.resp, r.e)
    }

    #[test]
    fn a_2_by_2_grid_multiplies_to_210() {
        // (2, 3) and (5, 7): column products (10, 21), total 210.
        let r = prove(scalars(&[&[2, 3], &[5, 7]]), None);
        assert!(holds(&r, 210));
        assert!(!holds(&r, 211));
    }

    #[test]
    fn a_single_row_uses_s5_directly() {
        let r = prove(scalars(&[&[2, 3, 5]]), None);
        assert!(r.first.c_p.is_none() && r.second.zero.is_none());
        assert!(holds(&r, 30));
        assert!(!holds(&r, 31));
    }

    #[test]
    fn a_4_by_3_grid_verifies() {
        let r = prove(scalars(&[&[2, 3, 5], &[7, 11, 13], &[1, 1, 2], &[1, 1, 1]]), None);
        assert!(holds(&r, 2 * 3 * 5 * 7 * 11 * 13 * 2));
    }

    #[test]
    fn a_large_random_grid_verifies() {
        let w: Vec<Vec<Scalar>> = (0..16).map(|_| (0..63).map(|_| random_blinding()).collect()).collect();
        let beta: Scalar = w.iter().flatten().product();
        let r = prove(w, None);
        assert!(check(&r.key, r.n, &r.c_w, beta, &r.first, r.x_h, r.y_h, &r.second, &r.resp, r.e));
    }

    #[test]
    fn fake_column_products_with_the_right_total_fail() {
        // True column products (10, 21); the prover claims (14, 15), which also
        // multiply to 210. S5 alone would accept; S3 catches it.
        let r = prove(scalars(&[&[2, 3], &[5, 7]]), Some(Some(scalars(&[&[14, 15]]).remove(0))));
        assert!(!holds(&r, 210));
    }

    #[test]
    fn a_swapped_row_commitment_fails() {
        let mut r = prove(scalars(&[&[2, 3], &[5, 7]]), None);
        r.c_w[1] = com_v(&r.key, &scalars(&[&[7, 5]])[0], &random_blinding());
        assert!(!holds(&r, 210));
    }

    #[test]
    fn a_proof_of_the_wrong_shape_is_rejected() {
        // A single-row proof does not pass for two rows, and the other way round.
        let one = prove(scalars(&[&[2, 3, 5]]), None);
        let two = prove(scalars(&[&[2, 3], &[5, 1]]), None);
        let c_two = two.c_w.clone();
        assert!(!check(&one.key, 3, &c_two, Scalar::from(30u64), &one.first, one.x_h, one.y_h, &one.second, &one.resp, one.e));
        assert!(!check(&two.key, 2, &c_two[..1], Scalar::from(30u64), &two.first, two.x_h, two.y_h, &two.second, &two.resp, two.e));
    }
}
