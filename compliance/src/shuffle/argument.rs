use curve25519_dalek::{
    RistrettoPoint, Scalar,
    ristretto::CompressedRistretto,
    traits::{Identity, VartimeMultiscalarMul},
};
use ibc::commitment::{Commitment, random_blinding};
use ibc::params::PublicParams;
use merlin::Transcript;

use super::multiexp::{self, MultiExpFirst, MultiExpResponse};
use super::product::{self, ProductFirst, ProductResponse, ProductSecond};
use super::{Grid, com_v};
use crate::hash::compress;
use crate::params::ShuffleKey;

// S1, the shuffle argument (shuffle_argument.md section 3). For lists of N pairs:
//   C_out[j] = C_in[perm[j]] + delta_j*g_ran   and   D_out[j] = D_in[perm[j]] + eta_j*g_ran
// with ONE permutation for both lists. perm is 0-based here; the protocol's positions
// are 1-based, so a_j = perm[j] + 1 and b_j = x^(perm[j] + 1).
// Non-interactive: every challenge comes from one Merlin transcript that starts with
// the round's ctx and the whole statement (decision 24). The caller passes the four
// lists also compressed, in the order c_in, d_in, c_out, d_out: in a round it has
// those bytes already, from stmt (decision 34).
pub struct ShuffleProof {
    pub c_a: Vec<RistrettoPoint>, // move 1: the permutation, one commitment per row
    pub c_b: Vec<RistrettoPoint>, // move 3: x^(position), one commitment per row
    pub product_first: ProductFirst,     // move 5
    pub product_second: ProductSecond,   // move 7
    pub multiexp_first: MultiExpFirst,   // move 7
    pub product_resp: ProductResponse,   // move 9
    pub multiexp_resp: MultiExpResponse, // move 9
}

fn challenge(t: &mut Transcript, label: &'static [u8]) -> Scalar {
    let mut buf = [0u8; 64];
    t.challenge_bytes(label, &mut buf);
    Scalar::from_bytes_mod_order_wide(&buf)
}

fn append_compressed(t: &mut Transcript, label: &'static [u8], ps: &[CompressedRistretto]) {
    t.append_u64(b"len", ps.len() as u64);
    for p in ps {
        t.append_message(label, p.as_bytes());
    }
}

fn append_points(t: &mut Transcript, label: &'static [u8], ps: &[RistrettoPoint]) {
    append_compressed(t, label, &ps.iter().map(|p| p.compress()).collect::<Vec<_>>());
}

// Everything the shuffle is about goes in before the first challenge.
fn start(ctx: &[u8], grid: Grid, lists: [&[CompressedRistretto]; 4]) -> Transcript {
    let mut t = Transcript::new(b"compliance/v1/shuffle");
    t.append_message(b"ctx", ctx);
    t.append_u64(b"m", grid.m as u64);
    t.append_u64(b"n", grid.n as u64);
    for (label, list) in [b"c_in" as &'static [u8], b"d_in", b"c_out", b"d_out"].into_iter().zip(lists) {
        append_compressed(&mut t, label, list);
    }
    t
}

// The bytes the transcript absorbs must be the lists the proof is about.
fn same_lists(encoded: &[&[CompressedRistretto]; 4], lists: [&[Commitment]; 4]) -> bool {
    encoded.iter().zip(lists).all(|(e, l)| *e == compress(l).as_slice())
}

fn append_product_first(t: &mut Transcript, f: &ProductFirst) {
    append_points(t, b"c_p", &f.c_p.iter().copied().collect::<Vec<_>>());
    append_points(t, b"c_q", &f.c_q_mid);
}

fn append_move_7(t: &mut Transcript, ps: &ProductSecond, mf: &MultiExpFirst) {
    if let Some(z) = &ps.zero {
        append_points(t, b"zero", &[z.c_a0, z.c_bm]);
        append_points(t, b"zero_d", &z.c_d);
    }
    append_points(t, b"svp", &[ps.svp.c_d, ps.svp.c_delta, ps.svp.c_gamma]);
    append_points(t, b"me", &[mf.c_a0]);
    append_points(t, b"me_c", &mf.e_c);
    append_points(t, b"me_d", &mf.e_d);
}

fn points(cs: &[Commitment]) -> Vec<RistrettoPoint> {
    cs.iter().map(|c| c.0).collect()
}

// Padding (shuffle_argument.md section 0): identity points that stay in place.
fn padded(cs: &[Commitment], len: usize) -> Vec<RistrettoPoint> {
    cs.iter().map(|c| c.0).chain(std::iter::repeat(RistrettoPoint::identity())).take(len).collect()
}

fn powers(x: Scalar, count: usize) -> Vec<Scalar> {
    std::iter::successors(Some(Scalar::ONE), |p| Some(p * x)).take(count).collect()
}

// beta = prod_{k=1..N} (y*k + x^k - z): what prod_j (y*a_j + b_j - z) must equal when
// a is a permutation of 1..N and b_j = x^(a_j).
fn target(x: Scalar, y: Scalar, z: Scalar, big_n: usize) -> Scalar {
    let xp = powers(x, big_n + 1);
    (1..=big_n).map(|k| y * Scalar::from(k as u64) + xp[k] - z).product()
}

impl ShuffleProof {
    pub fn size_bytes(&self) -> usize {
        32 * (self.c_a.len() + self.c_b.len())
            + self.product_first.size_bytes()
            + self.product_second.size_bytes()
            + self.multiexp_first.size_bytes()
            + self.product_resp.size_bytes()
            + self.multiexp_resp.size_bytes()
    }

    #[allow(clippy::too_many_arguments)]
    pub fn prove(
        key: &ShuffleKey,
        pp: &PublicParams,
        grid: Grid,
        c_in: &[Commitment],
        d_in: &[Commitment],
        c_out: &[Commitment],
        d_out: &[Commitment],
        encoded: [&[CompressedRistretto]; 4],
        perm: &[usize],
        delta: &[Scalar],
        eta: &[Scalar],
        ctx: &[u8],
    ) -> Self {
        let n_real = c_in.len();
        assert!(d_in.len() == n_real && c_out.len() == n_real && d_out.len() == n_real);
        assert!(perm.len() == n_real && delta.len() == n_real && eta.len() == n_real);
        assert_eq!(grid, Grid::with_rows(n_real, grid.m), "grid does not fit N");
        debug_assert!(same_lists(&encoded, [c_in, d_in, c_out, d_out]), "encoded must be the four lists");
        let big_n = grid.len();

        // Step 1: pad. Padding positions map to themselves and are not re-randomised.
        let perm: Vec<usize> = perm.iter().copied().chain(n_real..big_n).collect();
        let delta: Vec<Scalar> = delta.iter().copied().chain(std::iter::repeat(Scalar::ZERO)).take(big_n).collect();
        let eta: Vec<Scalar> = eta.iter().copied().chain(std::iter::repeat(Scalar::ZERO)).take(big_n).collect();
        let mut t = start(ctx, grid, encoded);

        // Steps 2-3: commit to the permutation.
        let a: Vec<Scalar> = perm.iter().map(|&p| Scalar::from((p + 1) as u64)).collect();
        let r_a: Vec<Scalar> = (0..grid.m).map(|_| random_blinding()).collect();
        let c_a: Vec<RistrettoPoint> = grid.rows(&a).iter().zip(&r_a).map(|(row, r)| com_v(key, row, r)).collect();
        append_points(&mut t, b"c_a", &c_a);
        let x = challenge(&mut t, b"x");

        // Steps 4-5: commit to x^(position).
        let xp = powers(x, big_n + 1);
        let b: Vec<Scalar> = perm.iter().map(|&p| xp[p + 1]).collect();
        let s_b: Vec<Scalar> = (0..grid.m).map(|_| random_blinding()).collect();
        let b_rows = grid.rows(&b);
        let c_b: Vec<RistrettoPoint> = b_rows.iter().zip(&s_b).map(|(row, s)| com_v(key, row, s)).collect();
        append_points(&mut t, b"c_b", &c_b);
        let y = challenge(&mut t, b"y");
        let z = challenge(&mut t, b"z");

        // Step 6: the rows of w = y*a + b - z, opened by y*r_A + s_B.
        let w: Vec<Scalar> = a.iter().zip(&b).map(|(ai, bi)| y * ai + bi - z).collect();
        let u: Vec<Scalar> = r_a.iter().zip(&s_b).map(|(r, s)| y * r + s).collect();

        // Step 10, move 5: the product argument's first message.
        let (product_first, pst) = product::commit(key, &grid.rows(&w), &u);
        append_product_first(&mut t, &product_first);
        let x_h = challenge(&mut t, b"x_h");
        let y_h = challenge(&mut t, b"y_h");

        // Move 7: product (S3/S4, S5) and multi-exponentiation (S6) first messages.
        let (product_second, pst2) = product::commit_second(pst, key, x_h, y_h);
        let kappa_c = -b.iter().zip(&delta).map(|(bj, dj)| bj * dj).sum::<Scalar>(); // step 9
        let kappa_d = -b.iter().zip(&eta).map(|(bj, hj)| bj * hj).sum::<Scalar>();
        let c_rows = grid.rows(&padded(c_out, big_n));
        let d_rows = grid.rows(&padded(d_out, big_n));
        let (multiexp_first, mst) = multiexp::commit(key, &pp.g_ran, &c_rows, &d_rows, &b_rows, &s_b, kappa_c, kappa_d);
        append_move_7(&mut t, &product_second, &multiexp_first);
        let e = challenge(&mut t, b"e");

        // Move 9.
        ShuffleProof {
            c_a,
            c_b,
            product_first,
            product_second,
            multiexp_first,
            product_resp: product::respond(pst2, e),
            multiexp_resp: multiexp::respond(mst, e),
        }
    }

    // Steps 11-17.
    #[allow(clippy::too_many_arguments)]
    pub fn verify(
        &self,
        key: &ShuffleKey,
        pp: &PublicParams,
        grid: Grid,
        c_in: &[Commitment],
        d_in: &[Commitment],
        c_out: &[Commitment],
        d_out: &[Commitment],
        encoded: [&[CompressedRistretto]; 4],
        ctx: &[u8],
    ) -> bool {
        let n_real = c_in.len();
        if n_real < 2 || d_in.len() != n_real || c_out.len() != n_real || d_out.len() != n_real {
            return false;
        }
        if grid.m == 0 || grid != Grid::with_rows(n_real, grid.m) || key.g.len() < grid.n {
            return false;
        }
        if self.c_a.len() != grid.m || self.c_b.len() != grid.m {
            return false;
        }
        debug_assert!(same_lists(&encoded, [c_in, d_in, c_out, d_out]), "encoded must be the four lists");
        let big_n = grid.len();

        // 13: the same transcript, the same challenges.
        let mut t = start(ctx, grid, encoded);
        append_points(&mut t, b"c_a", &self.c_a);
        let x = challenge(&mut t, b"x");
        append_points(&mut t, b"c_b", &self.c_b);
        let y = challenge(&mut t, b"y");
        let z = challenge(&mut t, b"z");
        append_product_first(&mut t, &self.product_first);
        let x_h = challenge(&mut t, b"x_h");
        let y_h = challenge(&mut t, b"y_h");
        append_move_7(&mut t, &self.product_second, &self.multiexp_first);
        let e = challenge(&mut t, b"e");

        // 14: c_w = y*c_A + c_B - z*(g_1 + ... + g_n), built without the prover.
        let g_sum: RistrettoPoint = key.g[..grid.n].iter().sum();
        let c_w: Vec<RistrettoPoint> = self.c_a.iter().zip(&self.c_b).map(|(ca, cb)| y * ca + cb - z * g_sum).collect();

        // 15-16: the public target and the weighted sums of the inputs.
        let beta = target(x, y, z, big_n);
        let xp = powers(x, n_real + 1);
        let y_c = RistrettoPoint::vartime_multiscalar_mul(&xp[1..], &points(c_in));
        let y_d = RistrettoPoint::vartime_multiscalar_mul(&xp[1..], &points(d_in));

        // 17.
        let c_rows = grid.rows(&padded(c_out, big_n));
        let d_rows = grid.rows(&padded(d_out, big_n));
        product::check(key, grid.n, &c_w, beta, &self.product_first, x_h, y_h, &self.product_second, &self.product_resp, e)
            && multiexp::check(key, &pp.g_ran, &c_rows, &d_rows, &self.c_b, &y_c, &y_d, &self.multiexp_first, &self.multiexp_resp, e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ibc::commitment::{Opening, commit};
    use ibc::params::{hash_identity, value_to_scalar};
    use rand_core::{OsRng, RngCore};

    const CTX: &[u8] = b"round-1";

    struct Shuffled {
        pp: PublicParams,
        c_in: Vec<Commitment>,
        d_in: Vec<Commitment>,
        c_out: Vec<Commitment>,
        d_out: Vec<Commitment>,
        perm: Vec<usize>,
        delta: Vec<Scalar>,
        eta: Vec<Scalar>,
    }

    fn random_perm(n: usize) -> Vec<usize> {
        let mut v: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            v.swap(i, (OsRng.next_u64() % (i as u64 + 1)) as usize);
        }
        v
    }

    // alice's pairs: c with her id and an amount, d with a date and no id.
    fn shuffled(n: usize) -> Shuffled {
        let pp = PublicParams::setup();
        let id = hash_identity(b"alice");
        let c_in: Vec<Commitment> = (0..n as u64)
            .map(|k| commit(&pp, &Opening { id, val: value_to_scalar(100 + k), blinding: random_blinding() }))
            .collect();
        let d_in: Vec<Commitment> = (0..n as u64)
            .map(|k| Commitment(value_to_scalar(20_000 + k) * pp.g_val + random_blinding() * pp.g_ran))
            .collect();
        let perm = random_perm(n);
        let delta: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
        let eta: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
        let c_out = (0..n).map(|j| Commitment(c_in[perm[j]].0 + delta[j] * pp.g_ran)).collect();
        let d_out = (0..n).map(|j| Commitment(d_in[perm[j]].0 + eta[j] * pp.g_ran)).collect();
        Shuffled { pp, c_in, d_in, c_out, d_out, perm, delta, eta }
    }

    fn encoded(s: &Shuffled) -> [Vec<CompressedRistretto>; 4] {
        [compress(&s.c_in), compress(&s.d_in), compress(&s.c_out), compress(&s.d_out)]
    }

    fn prove(s: &Shuffled, grid: Grid, key: &ShuffleKey) -> ShuffleProof {
        let enc = encoded(s);
        ShuffleProof::prove(key, &s.pp, grid, &s.c_in, &s.d_in, &s.c_out, &s.d_out, enc.each_ref().map(Vec::as_slice), &s.perm, &s.delta, &s.eta, CTX)
    }

    fn verify(p: &ShuffleProof, s: &Shuffled, grid: Grid, key: &ShuffleKey, ctx: &[u8]) -> bool {
        let enc = encoded(s);
        p.verify(key, &s.pp, grid, &s.c_in, &s.d_in, &s.c_out, &s.d_out, enc.each_ref().map(Vec::as_slice), ctx)
    }

    #[test]
    fn honest_shuffles_verify_for_many_sizes() {
        // N = 2 and 3 run on one row; 10 pads a 3 x 4 grid; 257 uses m = 16.
        for n in [2, 3, 4, 7, 10, 64, 257] {
            let s = shuffled(n);
            let grid = Grid::for_len(n);
            let key = ShuffleKey::new(&s.pp, grid.n);
            let p = prove(&s, grid, &key);
            assert!(verify(&p, &s, grid, &key, CTX), "N = {n}, grid {grid:?}");
        }
    }

    #[test]
    fn experiment_grids_verify() {
        // Decision 18f: m is swept in the experiments.
        let s = shuffled(100);
        for m in [1, 4, 16, 32] {
            let grid = Grid::with_rows(100, m);
            let key = ShuffleKey::new(&s.pp, grid.n);
            let p = prove(&s, grid, &key);
            assert!(verify(&p, &s, grid, &key, CTX), "m = {m}");
        }
    }

    #[test]
    fn a_dropped_and_replaced_record_fails() {
        // PayPay drops one of alice's records and puts a fresh commitment in its
        // place, then proves as if nothing happened.
        let mut s = shuffled(10);
        let grid = Grid::for_len(10);
        let key = ShuffleKey::new(&s.pp, grid.n);
        s.c_out[4] = commit(&s.pp, &Opening { id: hash_identity(b"alice"), val: value_to_scalar(1), blinding: random_blinding() });
        let p = prove(&s, grid, &key);
        assert!(!verify(&p, &s, grid, &key, CTX));
    }

    #[test]
    fn a_duplicated_record_fails() {
        // One record shows up twice and another vanishes: the map is not a
        // permutation, and the product argument rejects it.
        let mut s = shuffled(10);
        let grid = Grid::for_len(10);
        let key = ShuffleKey::new(&s.pp, grid.n);
        s.perm[3] = s.perm[2];
        s.c_out[3] = Commitment(s.c_in[s.perm[3]].0 + s.delta[3] * s.pp.g_ran);
        s.d_out[3] = Commitment(s.d_in[s.perm[3]].0 + s.eta[3] * s.pp.g_ran);
        let p = prove(&s, grid, &key);
        assert!(!verify(&p, &s, grid, &key, CTX));
    }

    #[test]
    fn dates_moved_differently_from_amounts_fail() {
        // Kresna's limitation_ages_can_be_paired_with_the_wrong_transaction: here
        // re-pairing a date with another amount breaks the shared permutation.
        let mut s = shuffled(10);
        let grid = Grid::for_len(10);
        let key = ShuffleKey::new(&s.pp, grid.n);
        s.d_out.swap(0, 1);
        let p = prove(&s, grid, &key);
        assert!(!verify(&p, &s, grid, &key, CTX));
    }

    #[test]
    fn a_proof_does_not_move_to_another_round_or_other_lists() {
        let s = shuffled(10);
        let grid = Grid::for_len(10);
        let key = ShuffleKey::new(&s.pp, grid.n);
        let p = prove(&s, grid, &key);
        assert!(verify(&p, &s, grid, &key, CTX));
        assert!(!verify(&p, &s, grid, &key, b"round-2"));

        let mut reordered = shuffled(10);
        reordered.c_in = s.c_in.iter().rev().copied().collect();
        reordered.d_in = s.d_in.iter().rev().copied().collect();
        reordered.c_out = s.c_out.clone();
        reordered.d_out = s.d_out.clone();
        reordered.pp = s.pp;
        assert!(!verify(&p, &reordered, grid, &key, CTX));
    }

    #[test]
    fn a_proof_for_one_grid_does_not_pass_as_another() {
        let s = shuffled(100);
        let key = ShuffleKey::new(&s.pp, 100);
        let p = prove(&s, Grid::with_rows(100, 4), &key);
        assert!(verify(&p, &s, Grid::with_rows(100, 4), &key, CTX));
        assert!(!verify(&p, &s, Grid::with_rows(100, 5), &key, CTX));
    }

    #[test]
    fn sizes_match_the_formulas() {
        // m >= 2: 32*(9m + 5n + 11) bytes. m = 1: 32*(3n + 13), the shape of the
        // single-row prototype measured in experiment/bench_shuffle.
        let s = shuffled(257);
        let grid = Grid::for_len(257); // 16 x 17
        let key = ShuffleKey::new(&s.pp, 257);
        assert_eq!(prove(&s, grid, &key).size_bytes(), 32 * (9 * 16 + 5 * 17 + 11));

        let one = Grid::with_rows(257, 1);
        assert_eq!(prove(&s, one, &key).size_bytes(), 32 * (3 * 257 + 13));
    }
}
