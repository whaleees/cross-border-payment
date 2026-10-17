use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use curve25519_dalek::{RistrettoPoint, Scalar, traits::Identity};
use ibc::commitment::Commitment;
use ibc::params::PublicParams;
use merlin::Transcript;

use crate::params::{DATE_BITS, VALUE_BITS};

// Bulletproofs over Kresna's generators (decision 12). With B = g_val and
// B_blinding = g_ran, a range-proof commitment v*g_val + gamma*g_ran is exactly an
// IBC commitment with id = 0, so Pi.VEq can bridge it to a three-basis one.
#[derive(Clone)]
pub struct RangeKey {
    pub pc: PedersenGens,
    pub bp: BulletproofGens,
}

impl RangeKey {
    // Room for up to `values` numbers in one aggregated proof.
    pub fn new(pp: &PublicParams, values: usize) -> Self {
        RangeKey {
            pc: PedersenGens { B: pp.g_val, B_blinding: pp.g_ran },
            bp: BulletproofGens::new(VALUE_BITS, values.max(1).next_power_of_two()),
        }
    }

    // Decision 28: make room when a round needs more numbers in one proof. The
    // generators are derived per party index, so the existing ones do not change.
    pub fn ensure(&mut self, values: usize) {
        let needed = values.max(1).next_power_of_two();
        if self.bp.party_capacity < needed {
            self.bp = BulletproofGens::new(VALUE_BITS, needed);
        }
    }
}

// What the prover knows behind a commitment v*g_val + blinding*g_ran.
#[derive(Clone, Copy, Debug)]
pub struct Opened {
    pub v: u64,
    pub blinding: Scalar,
}

// Every range proof starts from the round's ctx (decision 24), so it cannot be
// replayed in another round or for another statement.
fn transcript(ctx: &[u8]) -> Transcript {
    let mut t = Transcript::new(b"compliance/v1/bp");
    t.append_message(b"ctx", ctx);
    t
}

// Pads to a power of two with (0, 0), whose commitment is the identity point,
// which the verifier can add on its own side.
fn prove_padded(key: &RangeKey, mut values: Vec<u64>, mut blindings: Vec<Scalar>, bits: usize, ctx: &[u8]) -> Option<RangeProof> {
    let n = values.len().next_power_of_two();
    values.resize(n, 0);
    blindings.resize(n, Scalar::ZERO);
    RangeProof::prove_multiple(&key.bp, &key.pc, &mut transcript(ctx), &values, &blindings, bits).ok().map(|(p, _)| p)
}

fn verify_padded(key: &RangeKey, commitments: &[RistrettoPoint], proof: &RangeProof, bits: usize, ctx: &[u8]) -> bool {
    let n = commitments.len().next_power_of_two();
    let padded: Vec<_> = commitments
        .iter()
        .copied()
        .chain(std::iter::repeat(RistrettoPoint::identity()))
        .take(n)
        .map(|p| p.compress())
        .collect();
    proof.verify_multiple(&key.bp, &key.pc, &mut transcript(ctx), &padded, bits).is_ok()
}

// G5 step 18. For each tail date commitment d = t*g_val + s*g_ran, prove that
// theta - 1 - t is in [0, 2^16): the date is before theta, so the record expired.
// The committed number is held by (theta - 1)*g_val - d, with blinding -s.
// None if a date is not expired: no honest proof exists for it.
pub fn prove_expired(key: &RangeKey, theta: u64, tail: &[Opened], ctx: &[u8]) -> Option<RangeProof> {
    assert!(!tail.is_empty(), "no tail, no expiry proof (e = 0)");
    let values = tail.iter().map(|d| (theta - 1).checked_sub(d.v)).collect::<Option<Vec<u64>>>()?;
    let blindings = tail.iter().map(|d| -d.blinding).collect();
    prove_padded(key, values, blindings, DATE_BITS, ctx)
}

// G6 step 15. The verifier computes every (theta - 1)*g_val - d itself, from its
// own theta, so the prover cannot pick the number being range-checked.
pub fn verify_expired(key: &RangeKey, theta: u64, tail: &[Commitment], proof: &RangeProof, ctx: &[u8]) -> bool {
    if tail.is_empty() {
        return false;
    }
    let edge = (Scalar::from(theta) - Scalar::ONE) * key.pc.B;
    let xs: Vec<RistrettoPoint> = tail.iter().map(|d| edge - d.0).collect();
    verify_padded(key, &xs, proof, DATE_BITS, ctx)
}

// G5 step 19. One proof for: every new domestic amount, S, and B - S, all in
// [0, 2^64). The commitment to B - S is B*g_val - V_S, with blinding -gamma_S.
// None if S > B: the prover refuses earlier (G4 step 7) and has no proof anyway.
pub fn prove_amounts(key: &RangeKey, domestic: &[Opened], total: &Opened, limit: u64, ctx: &[u8]) -> Option<RangeProof> {
    let headroom = limit.checked_sub(total.v)?;
    let values = domestic.iter().map(|d| d.v).chain([total.v, headroom]).collect();
    let blindings = domestic.iter().map(|d| d.blinding).chain([total.blinding, -total.blinding]).collect();
    prove_padded(key, values, blindings, VALUE_BITS, ctx)
}

// G6 step 16. With S and B - S both in [0, 2^64) and B < 2^64, S <= B holds as
// integers: no value can wrap around the group order.
pub fn verify_amounts(key: &RangeKey, domestic: &[Commitment], total: &Commitment, limit: u64, proof: &RangeProof, ctx: &[u8]) -> bool {
    let headroom = Scalar::from(limit) * key.pc.B - total.0;
    let ws: Vec<RistrettoPoint> = domestic.iter().map(|d| d.0).chain([total.0, headroom]).collect();
    verify_padded(key, &ws, proof, VALUE_BITS, ctx)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ibc::commitment::{Opening, commit, random_blinding};

    const CTX: &[u8] = b"round-1";
    const THETA: u64 = 20_377; // window_start(20,741, 365): t_now 15 Oct 2026, T = 365

    fn setup(values: usize) -> (PublicParams, RangeKey) {
        let pp = PublicParams::setup();
        let key = RangeKey::new(&pp, values);
        (pp, key)
    }

    // A two-basis commitment v*g_val + blinding*g_ran and its opening.
    fn two_basis(pp: &PublicParams, v: Scalar) -> (Commitment, Scalar) {
        let blinding = random_blinding();
        (commit(pp, &Opening { id: Scalar::ZERO, val: v, blinding }), blinding)
    }

    fn dates(pp: &PublicParams, days: &[u64]) -> (Vec<Commitment>, Vec<Opened>) {
        days.iter()
            .map(|&t| {
                let (d, blinding) = two_basis(pp, Scalar::from(t));
                (d, Opened { v: t, blinding })
            })
            .unzip()
    }

    #[test]
    fn an_expired_tail_verifies_for_any_length() {
        // 1, 2, 3, 5 records: padded to 1, 2, 4, 8 with identity commitments.
        let (pp, key) = setup(8);
        for days in [vec![20_000], vec![19_000, 20_375], vec![1, 2, 3], vec![20_100; 5]] {
            let (ds, opened) = dates(&pp, &days);
            let proof = prove_expired(&key, THETA, &opened, CTX).unwrap();
            assert!(verify_expired(&key, THETA, &ds, &proof, CTX), "{} records", days.len());
        }
    }

    #[test]
    fn theta_minus_one_is_expired_and_theta_is_not() {
        // theta is the first day still counted.
        let (pp, key) = setup(1);
        let (ds, opened) = dates(&pp, &[THETA - 1]);
        let proof = prove_expired(&key, THETA, &opened, CTX).unwrap();
        assert!(verify_expired(&key, THETA, &ds, &proof, CTX));

        let (_, live) = dates(&pp, &[THETA]);
        assert!(prove_expired(&key, THETA, &live, CTX).is_none());
    }

    #[test]
    fn a_live_record_in_the_tail_cannot_be_proved_expired() {
        // The cheat this proof exists for: drop a record still inside the window.
        // theta - 1 - t is -31, which is p - 31 in the group: far outside [0, 2^16).
        // The prover tries the two numbers it could hope for; both fail.
        let (pp, key) = setup(2);
        let (ds, opened) = dates(&pp, &[19_000, THETA + 30]);
        let blindings = vec![-opened[0].blinding, -opened[1].blinding];

        let wrapped = vec![THETA - 1 - 19_000, (THETA - 1).wrapping_sub(THETA + 30)]; // 2^64 - 31
        let p = prove_padded(&key, wrapped, blindings.clone(), DATE_BITS, CTX).unwrap();
        assert!(!verify_expired(&key, THETA, &ds, &p, CTX));

        let zero = vec![THETA - 1 - 19_000, 0]; // claim it sits exactly on the edge
        let p = prove_padded(&key, zero, blindings, DATE_BITS, CTX).unwrap();
        assert!(!verify_expired(&key, THETA, &ds, &p, CTX));
    }

    #[test]
    fn the_verifier_uses_its_own_theta() {
        // A proof for theta does not pass a check against an earlier edge: the
        // verifier never takes the edge from the prover.
        let (pp, key) = setup(1);
        let (ds, opened) = dates(&pp, &[20_000]);
        let proof = prove_expired(&key, THETA, &opened, CTX).unwrap();
        assert!(!verify_expired(&key, 19_000, &ds, &proof, CTX));
    }

    #[test]
    fn an_expiry_proof_is_bound_to_the_context() {
        let (pp, key) = setup(1);
        let (ds, opened) = dates(&pp, &[20_000]);
        let proof = prove_expired(&key, THETA, &opened, b"round-1").unwrap();
        assert!(!verify_expired(&key, THETA, &ds, &proof, b"round-2"));
    }

    #[test]
    fn amounts_within_the_limit_verify() {
        // 0, 1 and 3 domestic records: 2, 3 and 5 numbers, padded to 2, 4 and 8.
        let (pp, key) = setup(8);
        for domestic in [vec![], vec![1_250], vec![300, 0, 9_999]] {
            let (vs, opened): (Vec<_>, Vec<_>) = domestic
                .iter()
                .map(|&v| {
                    let (c, blinding) = two_basis(&pp, Scalar::from(v));
                    (c, Opened { v, blinding })
                })
                .unzip();
            let s = 40_000 + domestic.iter().sum::<u64>();
            let (v_s, gamma) = two_basis(&pp, Scalar::from(s));
            let total = Opened { v: s, blinding: gamma };

            let proof = prove_amounts(&key, &opened, &total, 500_000, CTX).unwrap();
            assert!(verify_amounts(&key, &vs, &v_s, 500_000, &proof, CTX), "{} domestic", domestic.len());
        }
    }

    #[test]
    fn a_total_exactly_at_the_limit_passes() {
        let (pp, key) = setup(2);
        let (v_s, gamma) = two_basis(&pp, Scalar::from(500_000u64));
        let proof = prove_amounts(&key, &[], &Opened { v: 500_000, blinding: gamma }, 500_000, CTX).unwrap();
        assert!(verify_amounts(&key, &[], &v_s, 500_000, &proof, CTX));
    }

    #[test]
    fn a_total_above_the_limit_fails() {
        // S = 500,001 > B. The honest prover has no proof. A cheater that wraps
        // B - S in 64 bits commits to 2^64 - 1, while the verifier's B*g_val - V_S
        // holds p - 1: the two do not match.
        let (pp, key) = setup(2);
        let s = 500_001u64;
        let (v_s, gamma) = two_basis(&pp, Scalar::from(s));
        let total = Opened { v: s, blinding: gamma };
        assert!(prove_amounts(&key, &[], &total, 500_000, CTX).is_none());

        let forged = prove_padded(&key, vec![s, 500_000u64.wrapping_sub(s)], vec![gamma, -gamma], VALUE_BITS, CTX).unwrap();
        assert!(!verify_amounts(&key, &[], &v_s, 500_000, &forged, CTX));
    }

    #[test]
    fn a_negative_domestic_amount_fails() {
        // Kresna's limitation_a_negative_value_lowers_the_hidden_sum: an amount of
        // -7,000 (p - 7,000) would lower S. Its bridge copy holds p - 7,000, which no
        // 64-bit value matches, so the amounts proof fails.
        let (pp, key) = setup(4);
        let (v_neg, g_neg) = two_basis(&pp, -Scalar::from(7_000u64));
        let (v_s, gamma) = two_basis(&pp, Scalar::from(1_000u64));

        let forged = prove_padded(
            &key,
            vec![0u64.wrapping_sub(7_000), 1_000, 499_000],
            vec![g_neg, gamma, -gamma],
            VALUE_BITS,
            CTX,
        )
        .unwrap();
        assert!(!verify_amounts(&key, &[v_neg], &v_s, 500_000, &forged, CTX));
    }

    #[test]
    fn an_amounts_proof_is_bound_to_the_limit_and_the_context() {
        let (pp, key) = setup(2);
        let (v_s, gamma) = two_basis(&pp, Scalar::from(40_000u64));
        let proof = prove_amounts(&key, &[], &Opened { v: 40_000, blinding: gamma }, 500_000, CTX).unwrap();
        assert!(verify_amounts(&key, &[], &v_s, 500_000, &proof, CTX));
        assert!(!verify_amounts(&key, &[], &v_s, 300_000, &proof, CTX));
        assert!(!verify_amounts(&key, &[], &v_s, 500_000, &proof, b"round-2"));
    }

    #[test]
    fn the_key_grows_without_changing_earlier_proofs() {
        // A proof made with a small key still verifies with a grown one.
        let (pp, mut key) = setup(2);
        let (ds, opened) = dates(&pp, &[20_000, 20_001]);
        let proof = prove_expired(&key, THETA, &opened, CTX).unwrap();

        key.ensure(9);
        assert_eq!(key.bp.party_capacity, 16);
        assert!(verify_expired(&key, THETA, &ds, &proof, CTX));

        let (ds, opened) = dates(&pp, &[19_000; 9]);
        let proof = prove_expired(&key, THETA, &opened, CTX).unwrap();
        assert!(verify_expired(&key, THETA, &ds, &proof, CTX));
    }

    #[test]
    fn proof_sizes_follow_the_formula() {
        // (2*log2(bits * count) + 9) * 32 bytes, count padded to a power of two.
        let (pp, key) = setup(2);
        let (_, opened) = dates(&pp, &[20_000, 20_001]);
        let expiry = prove_expired(&key, THETA, &opened, CTX).unwrap();
        assert_eq!(expiry.to_bytes().len(), (2 * 5 + 9) * 32); // 16 * 2 = 2^5: 608 B

        let (_, gamma) = two_basis(&pp, Scalar::from(40_000u64));
        let amounts = prove_amounts(&key, &[], &Opened { v: 40_000, blinding: gamma }, 500_000, CTX).unwrap();
        assert_eq!(amounts.to_bytes().len(), (2 * 7 + 9) * 32); // 64 * 2 = 2^7: 736 B
    }
}
