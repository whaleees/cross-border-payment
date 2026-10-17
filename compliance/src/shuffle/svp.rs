use curve25519_dalek::{RistrettoPoint, Scalar};
use ibc::commitment::random_blinding;

use super::{com_v, com_v_public};
use crate::params::ShuffleKey;

// S5, single value product argument (Bayer-Groth full version 5.3): c_a = comV(a; r)
// and the product of every entry of a is beta. The prover opens masked versions of a
// and of its running products q (q_1 = a_1, q_l = q_{l-1}*a_l, q_n = beta); the
// verifier checks each step of the running product without seeing a or q.

// Sent before the challenge e.
#[derive(Clone, Copy, Debug)]
pub struct SvpFirst {
    pub c_d: RistrettoPoint,     // masks for a
    pub c_delta: RistrettoPoint, // the e^0 leftover of each running-product step
    pub c_gamma: RistrettoPoint, // the e^1 leftover
}

// Sent after e.
#[derive(Clone, Debug)]
pub struct SvpResponse {
    pub a_tilde: Vec<Scalar>, // e*a + d
    pub b_tilde: Vec<Scalar>, // e*q + delta
    pub r_tilde: Scalar,
    pub s_tilde: Scalar,
}

// The prover's secrets between commit and respond.
pub struct SvpState {
    a: Vec<Scalar>,
    r: Scalar,
    q: Vec<Scalar>,
    d: Vec<Scalar>,
    r_d: Scalar,
    delta: Vec<Scalar>,
    s_1: Scalar,
    s_x: Scalar,
}

impl SvpResponse {
    pub fn size_bytes(&self) -> usize {
        32 * (self.a_tilde.len() + self.b_tilde.len() + 2)
    }
}

fn running_products(a: &[Scalar]) -> Vec<Scalar> {
    a.iter()
        .scan(Scalar::ONE, |acc, ai| {
            *acc *= ai;
            Some(*acc)
        })
        .collect()
}

// Steps 1-5. Requires n >= 2: at n = 1 the two end checks (b~_1 = a~_1 and
// b~_n = e*beta) land on the same entry and cannot both hold.
pub fn commit(key: &ShuffleKey, a: &[Scalar], r: Scalar) -> (SvpFirst, SvpState) {
    commit_with_products(key, a, r, running_products(a))
}

// Split out so a test can hand in running products that are not the real ones.
fn commit_with_products(key: &ShuffleKey, a: &[Scalar], r: Scalar, q: Vec<Scalar>) -> (SvpFirst, SvpState) {
    let n = a.len();
    assert!(n >= 2, "S5 needs n >= 2");

    let d: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
    let r_d = random_blinding();

    // delta_1 = d_1 makes b~_1 = a~_1; delta_n = 0 makes b~_n = e*q_n.
    let mut delta: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
    delta[0] = d[0];
    delta[n - 1] = Scalar::ZERO;

    let big_delta: Vec<Scalar> = (0..n - 1).map(|l| -delta[l] * d[l + 1]).collect();
    let big_gamma: Vec<Scalar> =
        (0..n - 1).map(|l| delta[l + 1] - a[l + 1] * delta[l] - q[l] * d[l + 1]).collect();
    let (s_1, s_x) = (random_blinding(), random_blinding());

    let first = SvpFirst {
        c_d: com_v(key, &d, &r_d),
        c_delta: com_v(key, &big_delta, &s_1),
        c_gamma: com_v(key, &big_gamma, &s_x),
    };
    (first, SvpState { a: a.to_vec(), r, q, d, r_d, delta, s_1, s_x })
}

// Step 6.
pub fn respond(st: SvpState, e: Scalar) -> SvpResponse {
    SvpResponse {
        a_tilde: st.a.iter().zip(&st.d).map(|(a, d)| e * a + d).collect(),
        b_tilde: st.q.iter().zip(&st.delta).map(|(q, dl)| e * q + dl).collect(),
        r_tilde: e * st.r + st.r_d,
        s_tilde: e * st.s_x + st.s_1,
    }
}

// Steps 7-10, for a row of n entries committed in c_a.
pub fn check(key: &ShuffleKey, n: usize, c_a: &RistrettoPoint, beta: Scalar, first: &SvpFirst, resp: &SvpResponse, e: Scalar) -> bool {
    let (at, bt) = (&resp.a_tilde, &resp.b_tilde);
    if n < 2 || at.len() != n || bt.len() != n || key.g.len() < n {
        return false;
    }

    // 7: a~ really is e*a + d for the a inside c_a.
    if e * c_a + first.c_d != com_v_public(key, at, &resp.r_tilde) {
        return false;
    }

    // 8: e*b~_{l+1} - b~_l*a~_{l+1} = e^2*(q_{l+1} - q_l*a_{l+1}) + e*Gamma_l + Delta_l.
    // The e^2 part is zero only if q is the running product of a; Gamma and Delta
    // were fixed before e, so a non-zero e^2 part cannot be cancelled.
    let v: Vec<Scalar> = (0..n - 1).map(|l| e * bt[l + 1] - bt[l] * at[l + 1]).collect();
    if e * first.c_gamma + first.c_delta != com_v_public(key, &v, &resp.s_tilde) {
        return false;
    }

    // 9 and 10: the running product starts at a_1 and ends at beta.
    bt[0] == at[0] && bt[n - 1] == e * beta
}

#[cfg(test)]
mod tests {
    use super::*;
    use ibc::params::PublicParams;

    fn key(n: usize) -> ShuffleKey {
        ShuffleKey::new(&PublicParams::setup(), n)
    }

    fn scalars(xs: &[u64]) -> Vec<Scalar> {
        xs.iter().map(|&x| Scalar::from(x)).collect()
    }

    // Commit to a, run S5 for the claimed beta with challenge e, check with e_check.
    fn run(key: &ShuffleKey, a: &[Scalar], beta: Scalar, e: Scalar, e_check: Scalar) -> bool {
        let r = random_blinding();
        let c_a = com_v(key, a, &r);
        let (first, st) = commit(key, a, r);
        let resp = respond(st, e);
        check(key, a.len(), &c_a, beta, &first, &resp, e_check)
    }

    #[test]
    fn the_product_of_2_3_5_is_30() {
        let k = key(3);
        let e = random_blinding();
        assert!(run(&k, &scalars(&[2, 3, 5]), Scalar::from(30u64), e, e));
    }

    #[test]
    fn honest_proofs_verify_for_several_lengths() {
        for n in [2, 6, 63] {
            let k = key(n);
            let a: Vec<Scalar> = (0..n).map(|_| random_blinding()).collect();
            let beta: Scalar = a.iter().product();
            let e = random_blinding();
            assert!(run(&k, &a, beta, e, e), "n = {n}");
        }
    }

    #[test]
    fn a_wrong_target_fails() {
        let k = key(3);
        let e = random_blinding();
        assert!(!run(&k, &scalars(&[2, 3, 5]), Scalar::from(31u64), e, e));
    }

    #[test]
    fn faked_running_products_fail() {
        // To claim 31 the prover must end its running product at 31, so somewhere a
        // step q_{l+1} = q_l*a_{l+1} is false: here 6 * 5 is claimed to be 31.
        let k = key(3);
        let a = scalars(&[2, 3, 5]);
        let r = random_blinding();
        let c_a = com_v(&k, &a, &r);
        let (first, st) = commit_with_products(&k, &a, r, scalars(&[2, 6, 31]));
        let e = random_blinding();
        let resp = respond(st, e);
        assert!(!check(&k, 3, &c_a, Scalar::from(31u64), &first, &resp, e));
    }

    #[test]
    fn the_response_must_belong_to_the_committed_row() {
        // An honest proof for (2, 3, 5) does not transfer to another row with the
        // same product, (1, 6, 5).
        let k = key(3);
        let a = scalars(&[2, 3, 5]);
        let r = random_blinding();
        let (first, st) = commit(&k, &a, r);
        let e = random_blinding();
        let resp = respond(st, e);
        let other = com_v(&k, &scalars(&[1, 6, 5]), &r);
        assert!(!check(&k, 3, &other, Scalar::from(30u64), &first, &resp, e));
    }

    #[test]
    fn a_response_for_another_challenge_fails() {
        let k = key(3);
        assert!(!run(&k, &scalars(&[2, 3, 5]), Scalar::from(30u64), random_blinding(), random_blinding()));
    }

    #[test]
    fn tampered_first_messages_fail() {
        let k = key(3);
        let a = scalars(&[2, 3, 5]);
        let r = random_blinding();
        let c_a = com_v(&k, &a, &r);
        let (first, st) = commit(&k, &a, r);
        let e = random_blinding();
        let resp = respond(st, e);
        let x = random_blinding() * k.h;
        for bad in [
            SvpFirst { c_d: first.c_d + x, ..first },
            SvpFirst { c_delta: first.c_delta + x, ..first },
            SvpFirst { c_gamma: first.c_gamma + x, ..first },
        ] {
            assert!(!check(&k, 3, &c_a, Scalar::from(30u64), &bad, &resp, e));
        }
    }

    #[test]
    fn a_response_of_the_wrong_length_is_rejected() {
        let k = key(3);
        let a = scalars(&[2, 3, 5]);
        let r = random_blinding();
        let c_a = com_v(&k, &a, &r);
        let (first, st) = commit(&k, &a, r);
        let e = random_blinding();
        let mut resp = respond(st, e);
        resp.a_tilde.pop();
        assert!(!check(&k, 3, &c_a, Scalar::from(30u64), &first, &resp, e));
    }

    #[test]
    #[should_panic(expected = "S5 needs n >= 2")]
    fn a_single_entry_is_refused() {
        let k = key(1);
        commit(&k, &scalars(&[30]), random_blinding());
    }

    #[test]
    fn response_size_is_2n_plus_2_scalars() {
        // Plus 3 points in SvpFirst: 32*(2n + 5) bytes in all.
        let k = key(63);
        let a: Vec<Scalar> = (0..63).map(|_| random_blinding()).collect();
        let (_, st) = commit(&k, &a, random_blinding());
        assert_eq!(respond(st, random_blinding()).size_bytes(), 32 * (2 * 63 + 2));
    }
}
