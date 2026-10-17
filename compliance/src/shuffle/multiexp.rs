use curve25519_dalek::{
    RistrettoPoint, Scalar,
    traits::{Identity, VartimeMultiscalarMul},
};
use ibc::commitment::random_blinding;

use super::{com_v, com_v_public, msm_secret};
use crate::params::ShuffleKey;

// S6, multi-exponentiation argument for two lists (Bayer-Groth section 4,
// decisions 10 and 30). For output rows C_1..C_m and D_1..D_m and the rows b_i
// committed in c_B:
//   Y_C = sum_i <C_i, b_i> + kappa_C*g_ran   and   Y_D = sum_i <D_i, b_i> + kappa_D*g_ran
// Picture the table <C_i, A_j> with A_0 a fresh mask and A_j = b_j. Its main diagonal
// is the statement; the prover sends every other diagonal sum E_k (blinded along
// g_ran) so that one challenge e checks the whole table at once.
// Both lists use the same mask a_0 and the same opened a, hence the same b: the dates
// are shuffled with exactly the permutation of the amounts.
//
// 0-indexed: rows i = 0..m, columns j = 0..=m (A[0] = mask, A[j] = b[j-1]); the pair
// (i, j) sits on diagonal k = m - 1 + j - i, k = 0..2m-1, main diagonal k = m.

#[derive(Clone, Debug)]
pub struct MultiExpFirst {
    pub c_a0: RistrettoPoint,
    pub e_c: Vec<RistrettoPoint>, // E_C,k for k = 0..2m-1, skipping k = m
    pub e_d: Vec<RistrettoPoint>,
}

#[derive(Clone, Debug)]
pub struct MultiExpResponse {
    pub a: Vec<Scalar>, // sum_j e^j * A_j, shared by both lists
    pub r: Scalar,
    pub tau_c: Scalar,
    pub tau_d: Scalar,
}

pub struct MultiExpState {
    big_a: Vec<Vec<Scalar>>, // A_0 (mask), A_1..A_m = b
    r0: Scalar,
    s_b: Vec<Scalar>,
    tau_c: Vec<Scalar>, // per diagonal, zero at k = m
    tau_d: Vec<Scalar>,
    kappa_c: Scalar,
    kappa_d: Scalar,
}

impl MultiExpFirst {
    pub fn size_bytes(&self) -> usize {
        32 * (1 + self.e_c.len() + self.e_d.len())
    }
}

impl MultiExpResponse {
    pub fn size_bytes(&self) -> usize {
        32 * (self.a.len() + 3)
    }
}

fn powers(e: Scalar, count: usize) -> Vec<Scalar> {
    std::iter::successors(Some(Scalar::ONE), |p| Some(p * e)).take(count).collect()
}

// Diagonal k without its blinding: sum of <rows[i], A[j]> over m - 1 + j - i = k,
// as ONE multi-scalar multiplication (decision 10; the old code multiplied point by
// point). Through msm_secret, because A holds the secret permutation.
fn diagonal(rows: &[Vec<RistrettoPoint>], big_a: &[Vec<Scalar>], k: usize) -> RistrettoPoint {
    let m = rows.len();
    let pairs: Vec<(usize, usize)> = (0..m).filter_map(|i| (i + k + 1).checked_sub(m).map(|j| (i, j))).filter(|&(_, j)| j <= m).collect();
    // Collected first: the MSM needs iterators of known, equal length.
    let scalars: Vec<Scalar> = pairs.iter().flat_map(|&(_, j)| big_a[j].iter().copied()).collect();
    let points: Vec<RistrettoPoint> = pairs.iter().flat_map(|&(i, _)| rows[i].iter().copied()).collect();
    msm_secret(&scalars, &points)
}

// Steps 1-2. c_rows, d_rows: the output lists cut into m rows of n; b, s_b: the rows
// committed in c_B and their blindings.
#[allow(clippy::too_many_arguments)]
pub fn commit(
    key: &ShuffleKey,
    g_ran: &RistrettoPoint,
    c_rows: &[Vec<RistrettoPoint>],
    d_rows: &[Vec<RistrettoPoint>],
    b: &[Vec<Scalar>],
    s_b: &[Scalar],
    kappa_c: Scalar,
    kappa_d: Scalar,
) -> (MultiExpFirst, MultiExpState) {
    let m = c_rows.len();
    assert!(m >= 1 && d_rows.len() == m && b.len() == m && s_b.len() == m);
    let n = b[0].len();

    let a0: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
    let r0 = random_blinding();
    let c_a0 = com_v(key, &a0, &r0);
    let big_a: Vec<Vec<Scalar>> = std::iter::once(a0).chain(b.iter().cloned()).collect();

    let blind = |k: usize| if k == m { Scalar::ZERO } else { random_blinding() };
    let tau_c: Vec<Scalar> = (0..2 * m).map(blind).collect();
    let tau_d: Vec<Scalar> = (0..2 * m).map(blind).collect();

    let off_main = (0..2 * m).filter(|&k| k != m);
    let e_c = off_main.clone().map(|k| diagonal(c_rows, &big_a, k) + tau_c[k] * g_ran).collect();
    let e_d = off_main.map(|k| diagonal(d_rows, &big_a, k) + tau_d[k] * g_ran).collect();

    (MultiExpFirst { c_a0, e_c, e_d }, MultiExpState { big_a, r0, s_b: s_b.to_vec(), tau_c, tau_d, kappa_c, kappa_d })
}

// Step 3.
pub fn respond(st: MultiExpState, e: Scalar) -> MultiExpResponse {
    let m = st.big_a.len() - 1;
    let n = st.big_a[0].len();
    let ep = powers(e, 2 * m);

    let mut a = vec![Scalar::ZERO; n];
    for (j, row) in st.big_a.iter().enumerate() {
        for (acc, x) in a.iter_mut().zip(row) {
            *acc += ep[j] * x;
        }
    }
    let tau = |taus: &[Scalar], kappa: Scalar| -> Scalar {
        (0..2 * m).filter(|&k| k != m).map(|k| ep[k] * taus[k]).sum::<Scalar>() + ep[m] * kappa
    };
    MultiExpResponse {
        a,
        r: st.r0 + st.s_b.iter().enumerate().map(|(j, s)| ep[j + 1] * s).sum::<Scalar>(),
        tau_c: tau(&st.tau_c, st.kappa_c),
        tau_d: tau(&st.tau_d, st.kappa_d),
    }
}

// Check 5 or 6 for one list, as one MSM of size N + 2m + 1:
//   sum_{k != m} e^k E_k + e^m Y - tau*g_ran - sum_i e^(m-1-i) <rows[i], a> == 0
fn list_holds(g_ran: &RistrettoPoint, rows: &[Vec<RistrettoPoint>], y: &RistrettoPoint, es: &[RistrettoPoint], a: &[Scalar], tau: Scalar, ep: &[Scalar]) -> bool {
    let m = rows.len();
    let mut scalars: Vec<Scalar> = (0..2 * m).filter(|&k| k != m).map(|k| ep[k]).collect();
    let mut points: Vec<RistrettoPoint> = es.to_vec();
    scalars.extend([ep[m], -tau]);
    points.extend([*y, *g_ran]);
    for (i, row) in rows.iter().enumerate() {
        let w = ep[m - 1 - i];
        scalars.extend(a.iter().map(|al| -(w * al)));
        points.extend(row.iter().copied());
    }
    RistrettoPoint::vartime_multiscalar_mul(scalars, points) == RistrettoPoint::identity()
}

// Steps 4-6.
#[allow(clippy::too_many_arguments)]
pub fn check(
    key: &ShuffleKey,
    g_ran: &RistrettoPoint,
    c_rows: &[Vec<RistrettoPoint>],
    d_rows: &[Vec<RistrettoPoint>],
    c_b: &[RistrettoPoint],
    y_c: &RistrettoPoint,
    y_d: &RistrettoPoint,
    first: &MultiExpFirst,
    resp: &MultiExpResponse,
    e: Scalar,
) -> bool {
    let m = c_rows.len();
    if m == 0 || d_rows.len() != m || c_b.len() != m || first.e_c.len() != 2 * m - 1 || first.e_d.len() != 2 * m - 1 {
        return false;
    }
    let n = resp.a.len();
    if key.g.len() < n || c_rows.iter().chain(d_rows).any(|row| row.len() != n) {
        return false;
    }
    let ep = powers(e, 2 * m);

    // 4: a opens c_A0 + sum_j e^j * c_B,j, so it is built from the b inside c_B.
    let lhs = RistrettoPoint::vartime_multiscalar_mul(&ep[..=m], std::iter::once(&first.c_a0).chain(c_b));
    if lhs != com_v_public(key, &resp.a, &resp.r) {
        return false;
    }

    // 5 and 6.
    list_holds(g_ran, c_rows, y_c, &first.e_c, &resp.a, resp.tau_c, &ep)
        && list_holds(g_ran, d_rows, y_d, &first.e_d, &resp.a, resp.tau_d, &ep)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shuffle::Grid;
    use ibc::params::PublicParams;
    use rand_core::{OsRng, RngCore};

    // A shuffled pair of lists, as S1 hands it to S6. perm[j] is the 0-based input
    // behind output j; b_j = x^(perm[j]+1).
    struct Instance {
        key: ShuffleKey,
        g_ran: RistrettoPoint,
        c_out: Vec<RistrettoPoint>,
        d_out: Vec<RistrettoPoint>,
        b: Vec<Scalar>,
        s_b: Vec<Scalar>,
        c_b: Vec<RistrettoPoint>,
        y_c: RistrettoPoint,
        y_d: RistrettoPoint,
        kappa_c: Scalar,
        kappa_d: Scalar,
        grid: Grid,
    }

    fn random_perm(n: usize) -> Vec<usize> {
        let mut v: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            v.swap(i, (OsRng.next_u64() % (i as u64 + 1)) as usize);
        }
        v
    }

    fn instance(m: usize, n: usize) -> Instance {
        let pp = PublicParams::setup();
        let key = ShuffleKey::new(&pp, n);
        let grid = Grid { m, n };
        let big_n = grid.len();
        let pts = |k: usize| -> Vec<RistrettoPoint> { (0..k).map(|_| random_blinding() * pp.g_val + random_blinding() * pp.g_iden).collect() };
        let (c_in, d_in) = (pts(big_n), pts(big_n));
        let perm = random_perm(big_n);
        let delta: Vec<Scalar> = (0..big_n).map(|_| random_blinding()).collect();
        let eta: Vec<Scalar> = (0..big_n).map(|_| random_blinding()).collect();
        let c_out = (0..big_n).map(|j| c_in[perm[j]] + delta[j] * pp.g_ran).collect();
        let d_out = (0..big_n).map(|j| d_in[perm[j]] + eta[j] * pp.g_ran).collect();

        let x = random_blinding();
        let xp = powers(x, big_n + 1);
        let b: Vec<Scalar> = perm.iter().map(|&p| xp[p + 1]).collect();
        let y_c = RistrettoPoint::vartime_multiscalar_mul(&xp[1..], &c_in);
        let y_d = RistrettoPoint::vartime_multiscalar_mul(&xp[1..], &d_in);
        let kappa_c = -b.iter().zip(&delta).map(|(b, d)| b * d).sum::<Scalar>();
        let kappa_d = -b.iter().zip(&eta).map(|(b, h)| b * h).sum::<Scalar>();

        let s_b: Vec<Scalar> = (0..m).map(|_| random_blinding()).collect();
        let c_b = grid.rows(&b).iter().zip(&s_b).map(|(row, s)| com_v(&key, row, s)).collect();
        Instance { key, g_ran: pp.g_ran, c_out, d_out, b, s_b, c_b, y_c, y_d, kappa_c, kappa_d, grid }
    }

    fn prove(inst: &Instance, e: Scalar) -> (MultiExpFirst, MultiExpResponse) {
        let (cr, dr, br) = (inst.grid.rows(&inst.c_out), inst.grid.rows(&inst.d_out), inst.grid.rows(&inst.b));
        let (first, st) = commit(&inst.key, &inst.g_ran, &cr, &dr, &br, &inst.s_b, inst.kappa_c, inst.kappa_d);
        (first, respond(st, e))
    }

    fn holds(inst: &Instance, first: &MultiExpFirst, resp: &MultiExpResponse, e: Scalar) -> bool {
        let (cr, dr) = (inst.grid.rows(&inst.c_out), inst.grid.rows(&inst.d_out));
        check(&inst.key, &inst.g_ran, &cr, &dr, &inst.c_b, &inst.y_c, &inst.y_d, first, resp, e)
    }

    #[test]
    fn a_real_shuffle_of_both_lists_verifies() {
        for (m, n) in [(1, 4), (2, 3), (4, 5), (16, 8)] {
            let inst = instance(m, n);
            let e = random_blinding();
            let (first, resp) = prove(&inst, e);
            assert!(holds(&inst, &first, &resp, e), "m = {m}, n = {n}");
        }
    }

    #[test]
    fn a_replaced_output_fails() {
        // One output is a commitment that came from no input: the weighted sums no
        // longer match, whatever the prover answers.
        let mut inst = instance(4, 5);
        inst.c_out[7] = random_blinding() * inst.g_ran + inst.c_out[3];
        let e = random_blinding();
        let (first, resp) = prove(&inst, e);
        assert!(!holds(&inst, &first, &resp, e));
    }

    #[test]
    fn dates_shuffled_with_another_permutation_fail() {
        // Amounts and dates must move together. Shuffle the dates with a different
        // permutation while proving with the amounts' b: the D check fails.
        let mut inst = instance(4, 5);
        let n = inst.d_out.len();
        let other = random_perm(n);
        let d = inst.d_out.clone();
        inst.d_out = (0..n).map(|j| d[other[j]]).collect();
        let e = random_blinding();
        let (first, resp) = prove(&inst, e);
        assert!(!holds(&inst, &first, &resp, e));
    }

    #[test]
    fn a_different_b_than_the_one_in_c_b_fails() {
        // The verifier only knows b through c_B (shared with the product argument).
        let mut inst = instance(2, 3);
        inst.c_b[1] = com_v(&inst.key, &[Scalar::ONE; 3], &inst.s_b[1]);
        let e = random_blinding();
        let (first, resp) = prove(&inst, e);
        assert!(!holds(&inst, &first, &resp, e));
    }

    #[test]
    fn a_tampered_diagonal_or_another_e_fails() {
        let inst = instance(4, 5);
        let e = random_blinding();
        let (first, resp) = prove(&inst, e);
        assert!(holds(&inst, &first, &resp, e));
        assert!(!holds(&inst, &first, &resp, random_blinding()));

        let mut bad = first.clone();
        bad.e_d[2] += inst.g_ran;
        assert!(!holds(&inst, &bad, &resp, e));
    }

    #[test]
    fn wrong_lengths_are_rejected() {
        let inst = instance(2, 3);
        let e = random_blinding();
        let (first, mut resp) = prove(&inst, e);
        let mut short = first.clone();
        short.e_c.pop();
        assert!(!holds(&inst, &short, &resp, e));
        resp.a.pop();
        assert!(!holds(&inst, &first, &resp, e));
    }

    #[test]
    fn sizes_are_4m_minus_1_points_and_n_plus_3_scalars() {
        // One mask shared by both lists; separate diagonals and tau per list.
        let inst = instance(16, 8);
        let e = random_blinding();
        let (first, resp) = prove(&inst, e);
        assert_eq!(first.size_bytes(), 32 * (4 * 16 - 1));
        assert_eq!(resp.size_bytes(), 32 * (8 + 3));
    }

    #[test]
    fn every_pair_lands_on_exactly_one_diagonal() {
        // The diagonals partition the (m) x (m+1) table: computing every diagonal,
        // main one included, and adding them up equals the whole table.
        let inst = instance(3, 2);
        let rows = inst.grid.rows(&inst.c_out);
        let a: Vec<Vec<Scalar>> = (0..=3).map(|_| (0..2).map(|_| random_blinding()).collect()).collect();
        let by_diagonal: RistrettoPoint = (0..6).map(|k| diagonal(&rows, &a, k)).sum();
        let whole: RistrettoPoint = (0..3)
            .flat_map(|i| (0..=3).map(move |j| (i, j)))
            .map(|(i, j)| RistrettoPoint::vartime_multiscalar_mul(&a[j], &rows[i]))
            .sum();
        assert_eq!(by_diagonal, whole);
    }
}
