use curve25519_dalek::{
    RistrettoPoint, Scalar,
    traits::{Identity, VartimeMultiscalarMul},
};
use ibc::commitment::random_blinding;

use super::{com_v, com_v_public, msm_secret};
use crate::level::Level;
use crate::params::ShuffleKey;

// S6, multi-exponentiation argument (Bayer-Groth section 4, decisions 10 and 30).
// For each list L of output rows L_1..L_m and the rows b_i committed in c_B:
//   Y_L = sum_i <L_i, b_i> + kappa_L*g_ran
// Picture the table <L_i, A_j> with A_0 a fresh mask and A_j = b_j. Its main diagonal
// is the statement; the prover sends every other diagonal sum E_k (blinded along
// g_ran) so that one challenge e checks the whole table at once.
// The lists share the mask a_0 and the opened a, hence the same b: the dates are
// shuffled with exactly the permutation of the amounts. Before level B2 the lists are
// C and D (decision 30); from B2 on there is one, W = C + lambda*D (decision 35).
//
// 0-indexed: rows i = 0..m, columns j = 0..=m (A[0] = mask, A[j] = b[j-1]); the pair
// (i, j) sits on diagonal k = m - 1 + j - i, k = 0..2m-1, main diagonal k = m.

#[derive(Clone, Debug)]
pub struct MultiExpFirst {
    pub c_a0: RistrettoPoint,
    pub e: Vec<Vec<RistrettoPoint>>, // per list: E_k for k = 0..2m-1, skipping k = m
}

#[derive(Clone, Debug)]
pub struct MultiExpResponse {
    pub a: Vec<Scalar>, // sum_j e^j * A_j, shared by every list
    pub r: Scalar,
    pub tau: Vec<Scalar>, // per list
}

pub struct MultiExpState {
    big_a: Vec<Vec<Scalar>>, // A_0 (mask), A_1..A_m = b
    r0: Scalar,
    s_b: Vec<Scalar>,
    taus: Vec<Vec<Scalar>>, // per list, per diagonal, zero at k = m
    kappas: Vec<Scalar>,
}

// One list as the verifier checks it: its rows as a weighted sum of row sets, and its
// target Y. C alone or D alone before B2; C with weight 1 plus D with weight lambda
// from B2 on, so W is never added up point by point on the verifier's side.
pub struct Checked<'a> {
    pub parts: Vec<(&'a [Vec<RistrettoPoint>], Scalar)>,
    pub y: RistrettoPoint,
}

impl MultiExpFirst {
    pub fn size_bytes(&self) -> usize {
        32 * (1 + self.e.iter().map(Vec::len).sum::<usize>())
    }
}

impl MultiExpResponse {
    pub fn size_bytes(&self) -> usize {
        32 * (self.a.len() + 1 + self.tau.len())
    }
}

fn powers(e: Scalar, count: usize) -> Vec<Scalar> {
    std::iter::successors(Some(Scalar::ONE), |p| Some(p * e)).take(count).collect()
}

// From this many rows on, Karatsuba needs fewer inner products than the table
// itself: m + K(m) against m^2 (13 against 16 at m = 4, 10 against 9 at m = 3).
const KARATSUBA_FROM: usize = 4;

// Every diagonal k = 0..2m-1 without its blinding; the main one (k = m) is not used.
// Below level A1 the table is computed diagonal by diagonal, as before decision 35.
fn diagonals(rows: &[Vec<RistrettoPoint>], big_a: &[Vec<Scalar>], level: Level) -> Vec<RistrettoPoint> {
    if level < Level::A1 || rows.len() < KARATSUBA_FROM {
        diagonals_direct(rows, big_a)
    } else {
        diagonals_karatsuba(rows, big_a)
    }
}

fn diagonals_direct(rows: &[Vec<RistrettoPoint>], big_a: &[Vec<Scalar>]) -> Vec<RistrettoPoint> {
    let m = rows.len();
    (0..2 * m).map(|k| if k == m { RistrettoPoint::identity() } else { diagonal(rows, big_a, k) }).collect()
}

// Decision 35, A1. The diagonals are the coefficients of the product of
//   Q(X) = sum_i rows[i] X^(m-1-i)   and   P(X) = sum_j A[j] X^j,
// so split off A[0] (m inner products), and multiply Q by the rest with Karatsuba:
// three half-size products instead of four, joined by additions of public rows and
// of scalars. 97 inner products at m = 16 instead of 256. Nothing is multiplied by
// a small number, which costs as much as a full scalar in constant time; that is
// why the Toom-Cook prover in identity-binding-commitment gained nothing.
fn diagonals_karatsuba(rows: &[Vec<RistrettoPoint>], big_a: &[Vec<Scalar>]) -> Vec<RistrettoPoint> {
    let m = rows.len();
    let q: Vec<Vec<RistrettoPoint>> = rows.iter().rev().cloned().collect(); // q[t] = rows[m-1-t]
    let mut out = vec![RistrettoPoint::identity(); 2 * m];
    for (t, row) in q.iter().enumerate() {
        out[t] += msm_secret(&big_a[0], row);
    }
    for (k, z) in karatsuba(&q, &big_a[1..]).into_iter().enumerate() {
        out[k + 1] += z;
    }
    out
}

// Coefficients of sum_t q[t] X^t times sum_t a[t] X^t, pairing each point row with
// a scalar row by an inner product. q and a have the same length L; 2L - 1 results.
fn karatsuba(q: &[Vec<RistrettoPoint>], a: &[Vec<Scalar>]) -> Vec<RistrettoPoint> {
    let len = q.len();
    if len == 1 {
        return vec![msm_secret(&a[0], &q[0])];
    }
    let h = len.div_ceil(2);
    let (q_lo, q_hi) = q.split_at(h);
    let (a_lo, a_hi) = a.split_at(h);
    let z0 = karatsuba(q_lo, a_lo);
    let z2 = karatsuba(q_hi, a_hi);
    // The upper halves are one row shorter when len is odd: missing rows count as zero.
    let q_sum: Vec<Vec<RistrettoPoint>> = (0..h)
        .map(|t| match q_hi.get(t) {
            Some(hi) => q_lo[t].iter().zip(hi).map(|(x, y)| x + y).collect(),
            None => q_lo[t].clone(),
        })
        .collect();
    let a_sum: Vec<Vec<Scalar>> = (0..h)
        .map(|t| match a_hi.get(t) {
            Some(hi) => a_lo[t].iter().zip(hi).map(|(x, y)| x + y).collect(),
            None => a_lo[t].clone(),
        })
        .collect();
    let z1 = karatsuba(&q_sum, &a_sum);

    let zero = RistrettoPoint::identity();
    let mut out = vec![zero; 2 * len - 1];
    for (t, z) in z0.iter().enumerate() {
        out[t] += z;
    }
    for (t, z) in z2.iter().enumerate() {
        out[t + 2 * h] += z;
    }
    for (t, z) in z1.iter().enumerate() {
        out[t + h] += z - z0[t] - z2.get(t).unwrap_or(&zero);
    }
    out
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

// Steps 1-2. lists: each list of outputs cut into m rows of n, with its kappa; b, s_b:
// the rows committed in c_B and their blindings.
pub fn commit(
    key: &ShuffleKey,
    g_ran: &RistrettoPoint,
    lists: &[(&[Vec<RistrettoPoint>], Scalar)],
    b: &[Vec<Scalar>],
    s_b: &[Scalar],
    level: Level,
) -> (MultiExpFirst, MultiExpState) {
    let m = b.len();
    assert!(m >= 1 && s_b.len() == m && !lists.is_empty() && lists.iter().all(|(rows, _)| rows.len() == m));
    let n = b[0].len();

    let a0: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
    let r0 = random_blinding();
    let c_a0 = com_v(key, &a0, &r0);
    let big_a: Vec<Vec<Scalar>> = std::iter::once(a0).chain(b.iter().cloned()).collect();

    let blind = |k: usize| if k == m { Scalar::ZERO } else { random_blinding() };
    let mut e = Vec::new();
    let mut taus = Vec::new();
    for (rows, _) in lists {
        let tau: Vec<Scalar> = (0..2 * m).map(blind).collect();
        let diag = diagonals(rows, &big_a, level);
        e.push((0..2 * m).filter(|&k| k != m).map(|k| diag[k] + tau[k] * g_ran).collect());
        taus.push(tau);
    }
    let kappas = lists.iter().map(|(_, kappa)| *kappa).collect();
    (MultiExpFirst { c_a0, e }, MultiExpState { big_a, r0, s_b: s_b.to_vec(), taus, kappas })
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
        tau: st.taus.iter().zip(&st.kappas).map(|(taus, kappa)| tau(taus, *kappa)).collect(),
    }
}

// Check 5 or 6 for one list, as one MSM of size (parts * N) + 2m + 1:
//   sum_{k != m} e^k E_k + e^m Y - tau*g_ran - sum_i e^(m-1-i) <rows[i], a> == 0
// where rows[i] = sum over the parts of weight * part[i].
fn list_holds(g_ran: &RistrettoPoint, m: usize, list: &Checked, es: &[RistrettoPoint], a: &[Scalar], tau: Scalar, ep: &[Scalar]) -> bool {
    let mut scalars: Vec<Scalar> = (0..2 * m).filter(|&k| k != m).map(|k| ep[k]).collect();
    let mut points: Vec<RistrettoPoint> = es.to_vec();
    scalars.extend([ep[m], -tau]);
    points.extend([list.y, *g_ran]);
    for (rows, weight) in &list.parts {
        for (i, row) in rows.iter().enumerate() {
            let w = ep[m - 1 - i] * weight;
            scalars.extend(a.iter().map(|al| -(w * al)));
            points.extend(row.iter().copied());
        }
    }
    RistrettoPoint::vartime_multiscalar_mul(scalars, points) == RistrettoPoint::identity()
}

// Steps 4-6.
pub fn check(
    key: &ShuffleKey,
    g_ran: &RistrettoPoint,
    lists: &[Checked],
    c_b: &[RistrettoPoint],
    first: &MultiExpFirst,
    resp: &MultiExpResponse,
    e: Scalar,
) -> bool {
    let m = c_b.len();
    if m == 0 || lists.is_empty() || first.e.len() != lists.len() || resp.tau.len() != lists.len() {
        return false;
    }
    if first.e.iter().any(|es| es.len() != 2 * m - 1) {
        return false;
    }
    let n = resp.a.len();
    let rows = lists.iter().flat_map(|l| &l.parts).flat_map(|(rows, _)| rows.iter());
    if key.g.len() < n || lists.iter().flat_map(|l| &l.parts).any(|(rows, _)| rows.len() != m) || rows.clone().any(|row| row.len() != n) {
        return false;
    }
    let ep = powers(e, 2 * m);

    // 4: a opens c_A0 + sum_j e^j * c_B,j, so it is built from the b inside c_B.
    let lhs = RistrettoPoint::vartime_multiscalar_mul(&ep[..=m], std::iter::once(&first.c_a0).chain(c_b));
    if lhs != com_v_public(key, &resp.a, &resp.r) {
        return false;
    }

    // 5 and 6, one per list.
    lists.iter().zip(&first.e).zip(&resp.tau).all(|((list, es), tau)| list_holds(g_ran, m, list, es, &resp.a, *tau, &ep))
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

    // Two lists, C and D, as before level B2.
    fn prove(inst: &Instance, e: Scalar) -> (MultiExpFirst, MultiExpResponse) {
        let (cr, dr, br) = (inst.grid.rows(&inst.c_out), inst.grid.rows(&inst.d_out), inst.grid.rows(&inst.b));
        let (first, st) = commit(&inst.key, &inst.g_ran, &[(&cr[..], inst.kappa_c), (&dr[..], inst.kappa_d)], &br, &inst.s_b, Level::LATEST);
        (first, respond(st, e))
    }

    fn holds(inst: &Instance, first: &MultiExpFirst, resp: &MultiExpResponse, e: Scalar) -> bool {
        let (cr, dr) = (inst.grid.rows(&inst.c_out), inst.grid.rows(&inst.d_out));
        let lists = [Checked { parts: vec![(&cr[..], Scalar::ONE)], y: inst.y_c }, Checked { parts: vec![(&dr[..], Scalar::ONE)], y: inst.y_d }];
        check(&inst.key, &inst.g_ran, &lists, &inst.c_b, first, resp, e)
    }

    // One list W = C + lambda*D, as from level B2: proved on W's points, checked from
    // C and D with lambda folded into the scalars.
    fn prove_combined(inst: &Instance, lambda: Scalar, e: Scalar) -> (MultiExpFirst, MultiExpResponse) {
        let w: Vec<RistrettoPoint> = inst.c_out.iter().zip(&inst.d_out).map(|(c, d)| c + lambda * d).collect();
        let (wr, br) = (inst.grid.rows(&w), inst.grid.rows(&inst.b));
        let kappa = inst.kappa_c + lambda * inst.kappa_d;
        let (first, st) = commit(&inst.key, &inst.g_ran, &[(&wr[..], kappa)], &br, &inst.s_b, Level::LATEST);
        (first, respond(st, e))
    }

    fn holds_combined(inst: &Instance, lambda: Scalar, first: &MultiExpFirst, resp: &MultiExpResponse, e: Scalar) -> bool {
        let (cr, dr) = (inst.grid.rows(&inst.c_out), inst.grid.rows(&inst.d_out));
        let lists = [Checked { parts: vec![(&cr[..], Scalar::ONE), (&dr[..], lambda)], y: inst.y_c + lambda * inst.y_d }];
        check(&inst.key, &inst.g_ran, &lists, &inst.c_b, first, resp, e)
    }

    #[test]
    fn one_combined_list_verifies_and_still_ties_the_dates() {
        for (m, n) in [(1, 4), (2, 3), (4, 5), (16, 8)] {
            let inst = instance(m, n);
            let (lambda, e) = (random_blinding(), random_blinding());
            let (first, resp) = prove_combined(&inst, lambda, e);
            assert!(holds_combined(&inst, lambda, &first, &resp, e), "m = {m}, n = {n}");
            assert!(!holds_combined(&inst, random_blinding(), &first, &resp, e), "another lambda");
        }
        // Dates shuffled with another permutation than the amounts: W is no longer a
        // shuffle of C_in + lambda*D_in with one b, so the single check fails.
        let mut inst = instance(4, 5);
        let other = random_perm(inst.d_out.len());
        let d = inst.d_out.clone();
        inst.d_out = other.iter().map(|&p| d[p]).collect();
        let (lambda, e) = (random_blinding(), random_blinding());
        let (first, resp) = prove_combined(&inst, lambda, e);
        assert!(!holds_combined(&inst, lambda, &first, &resp, e));
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
        bad.e[1][2] += inst.g_ran;
        assert!(!holds(&inst, &bad, &resp, e));
    }

    #[test]
    fn wrong_lengths_are_rejected() {
        let inst = instance(2, 3);
        let e = random_blinding();
        let (first, mut resp) = prove(&inst, e);
        let mut short = first.clone();
        short.e[0].pop();
        assert!(!holds(&inst, &short, &resp, e));
        resp.a.pop();
        assert!(!holds(&inst, &first, &resp, e));
    }

    #[test]
    fn sizes_are_4m_minus_1_points_and_n_plus_3_scalars() {
        // One mask shared by both lists; separate diagonals and tau per list. With one
        // combined list (B2): 2m points and n + 2 scalars.
        let inst = instance(16, 8);
        let e = random_blinding();
        let (first, resp) = prove(&inst, e);
        assert_eq!(first.size_bytes(), 32 * (4 * 16 - 1));
        assert_eq!(resp.size_bytes(), 32 * (8 + 3));
        let (first, resp) = prove_combined(&inst, random_blinding(), e);
        assert_eq!(first.size_bytes(), 32 * (2 * 16));
        assert_eq!(resp.size_bytes(), 32 * (8 + 2));
    }

    #[test]
    fn karatsuba_gives_every_diagonal_of_the_table() {
        // Odd and even m, powers of two and not, and the small m where it is unused.
        let g = curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
        for (m, n) in [(1, 3), (2, 2), (3, 4), (4, 2), (5, 3), (7, 2), (8, 1), (15, 2), (16, 3), (17, 2)] {
            let rows: Vec<Vec<RistrettoPoint>> = (0..m).map(|_| (0..n).map(|_| random_blinding() * g).collect()).collect();
            let a: Vec<Vec<Scalar>> = (0..=m).map(|_| (0..n).map(|_| random_blinding()).collect()).collect();
            let fast = diagonals_karatsuba(&rows, &a);
            assert_eq!(fast.len(), 2 * m);
            for (k, d) in fast.iter().enumerate() {
                assert_eq!(*d, diagonal(&rows, &a, k), "m = {m}, n = {n}, k = {k}");
            }
        }
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
