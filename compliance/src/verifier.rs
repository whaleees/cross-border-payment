use std::collections::HashMap;

use curve25519_dalek::Scalar;
use curve25519_dalek::ristretto::CompressedRistretto;
use ed25519_dalek::{SigningKey, VerifyingKey};
use ibc::commitment::Commitment;
use ibc::params::value_to_scalar;
use rand_core::{OsRng, RngCore};

use crate::ctx::{BOTH, DATE, Round, STAGE_DOMESTIC, STAGE_EXPIRY, STAGE_MIDEQ, STAGE_NEW_PAIR, STAGE_SHUFFLE, STAGE_TAG, STAGE_TOTAL, VALUE};
use crate::operator::{Entry, Insert, NullifierSet, Registry, SignedRegistry};
use crate::package::{Package, Start, statement};
use crate::params::{Params, ShuffleKey, window_start};
use crate::range::{RangeKey, verify_amounts, verify_expired};
use crate::request::{Request, SignedRequest};
use crate::shuffle::Grid;
use crate::state_token::StateToken;

// The verifier's side of one round (alur_gabungan.md G3 steps 1-4, G6, G7, G9).
// It keeps no history of the user: only its open rounds and its pending tokens.

// Why a package was rejected. Any one of them rejects the payment; nothing is recorded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rejection {
    UnknownRound,      // no open request with this round_id (or it was already decided)
    UnknownSigner,     // G6.1: the old token names a kid the registry does not list
    BadToken,          // G6.3: the old list is not what that verifier signed
    WrongRho,          // G6.4: rho does not open cm
    SpentToken,        // G6.5: the token was spent before (an old list)
    AlreadyRegistered, // G8: the tag is in the nullifier set (a re-registration)
    BadTag,
    BadShape,          // G6.6: sizes, or proofs missing where they are required
    BadMIDEq,
    BadTxVer,
    BadDate,
    BadDomestic,
    BadSum,
    BadShuffle,
    BadExpiry,
    BadAmounts,
    DoubleSpend,       // G7.5: another verifier recorded the same entry first
}

// What G6 hands to G7 once every check passed.
pub struct Approved {
    round_id: [u8; 32],
    entry: Entry,
    front_c: Vec<CompressedRistretto>, // the front, compressed: what K' signs
    front_d: Vec<CompressedRistretto>,
    cm_next: [u8; 32],
}

#[derive(Clone)]
struct Waiting {
    token: StateToken,
    done: bool, // "final" in G7: the entry is recorded, the token may go out
}

// Clone lets a benchmark start every iteration from the same state.
#[derive(Clone)]
pub struct Verifier {
    kid: u32,
    sk: SigningKey,
    limit: u64,
    params: Params,
    registry: Registry,
    range_key: RangeKey,
    open: HashMap<[u8; 32], Request>, // asked, waiting for Phi
    pending: HashMap<[u8; 32], Waiting>, // "Tertunda": issued tokens, for resending
}

impl Verifier {
    // G0 step 12, plus a sanity check that the registry lists this verifier as itself.
    pub fn new(kid: u32, sk: SigningKey, signed: &SignedRegistry, operator_pk: &VerifyingKey) -> Option<Self> {
        if !signed.verify(operator_pk) {
            return None;
        }
        let me = *signed.registry.get(kid)?;
        if me.pk != sk.verifying_key() {
            return None;
        }
        let params = Params::setup();
        Some(Verifier {
            kid,
            sk,
            limit: me.limit,
            params,
            registry: signed.registry.clone(),
            range_key: RangeKey::new(&params.pp, 4),
            open: HashMap::new(),
            pending: HashMap::new(),
        })
    }

    // G3 steps 1-4. today is the verifier's own clock; the merchant supplied tid and v.
    pub fn ask(&mut self, tid: Commitment, v: u64, today: u32) -> SignedRequest {
        let mut round_id = [0u8; 32];
        OsRng.fill_bytes(&mut round_id);
        let x = Request { tid, v, t_now: today, period: self.registry.period_days, limit: self.limit, round_id, kid: self.kid };
        self.open.insert(round_id, x);
        x.sign(&self.sk)
    }

    // G6. ns is read only (a pre-check); the binding write happens in finish.
    pub fn check(&mut self, ns: &NullifierSet, round_id: &[u8; 32], pkg: &Package) -> Result<Approved, Rejection> {
        // Its own x, never values echoed by the prover. A round is decided once.
        let x = self.open.remove(round_id).ok_or(Rejection::UnknownRound)?;
        let pp = self.params.pp;
        let (d, p) = (&pkg.data, &pkg.proofs);
        // Every list compressed once; the token, stmt and the shuffle transcript all
        // reuse these bytes (decision 34).
        let enc = d.encode();

        // A: where the history starts.
        let entry = match &d.start {
            Start::Token { token, rho, .. } => {
                let signer = self.registry.get(token.kid).ok_or(Rejection::UnknownSigner)?;
                if !token.verify(&signer.pk, &enc.c_old, &enc.d_old) {
                    return Err(Rejection::BadToken);
                }
                let nf = token.open(rho).ok_or(Rejection::WrongRho)?;
                if ns.contains(&Entry::Nullifier(nf)) {
                    return Err(Rejection::SpentToken);
                }
                Entry::Nullifier(nf)
            }
            Start::First { tag } => {
                if ns.contains(&Entry::tag(tag)) {
                    return Err(Rejection::AlreadyRegistered);
                }
                Entry::tag(tag)
            }
        };

        // B: shape. Every list has its length, every proof is there exactly when needed.
        let (n_old, k) = (d.c_old().len(), d.c_dom.len());
        let n = d.n();
        let e = d.e as usize;
        let first = matches!(d.start, Start::First { .. });
        let shape = d.d_old().len() == n_old
            && d.d_dom.len() == k
            && d.v_dom.len() == k
            && p.domestic.len() == k
            && d.c_out.len() == n
            && d.d_out.len() == n
            && e < n
            && p.tag.is_some() == first
            && p.mideq.is_some() == (n_old + k >= 1)
            && p.shuffle.is_some() == (n >= 2)
            && p.expiry.is_some() == (e > 0);
        if !shape {
            return Err(Rejection::BadShape);
        }
        let theta = window_start(x.t_now, x.period);
        let d_ref = Commitment(Scalar::from(x.t_now) * pp.g_val);
        let (c_in, d_in) = d.inputs();

        // C: the round's statement, recomputed here.
        let round = Round { round_id: x.round_id, stmt: statement(&x, d, &enc) };

        if let (Start::First { tag }, Some(proof)) = (&d.start, &p.tag) {
            if !proof.verify(&self.params, &x.tid, tag, &round.ctx(STAGE_TAG, VALUE, 0)) {
                return Err(Rejection::BadTag);
            }
        }

        // D: every old and domestic amount belongs to tid's owner; this payment is v, today.
        if let Some(proof) = &p.mideq {
            let cs: Vec<Commitment> = [x.tid].into_iter().chain(d.c_old().iter().chain(&d.c_dom).copied()).collect();
            if !proof.verify(&pp, &cs, &round.ctx(STAGE_MIDEQ, VALUE, 0)) {
                return Err(Rejection::BadMIDEq);
            }
        }
        if !p.txver.verify(&pp, &x.tid, &d.c_tx, value_to_scalar(x.v), &round.ctx(STAGE_NEW_PAIR, VALUE, 0)) {
            return Err(Rejection::BadTxVer);
        }
        if !p.fulleq.verify(&pp, &d.d_tx, &d_ref, &round.ctx(STAGE_NEW_PAIR, DATE, 0)) {
            return Err(Rejection::BadDate);
        }

        // E: each domestic amount has a two-basis copy holding the same value.
        for (j, ((c, v), proof)) in d.c_dom.iter().zip(&d.v_dom).zip(&p.domestic).enumerate() {
            if !proof.verify(&pp, c, v, &round.ctx(STAGE_DOMESTIC, VALUE, j as u32 + 1)) {
                return Err(Rejection::BadDomestic);
            }
        }

        // F: V_S holds the total of the front, summed here (Lemma 5).
        let front_c = d.front().0;
        let c_sum = front_c.iter().skip(1).fold(front_c[0], |acc, c| acc + *c);
        if !p.sum.verify(&pp, &c_sum, &d.v_s, &round.ctx(STAGE_TOTAL, VALUE, 0)) {
            return Err(Rejection::BadSum);
        }

        // G: the outputs are the inputs, shuffled with one permutation, re-randomised.
        match &p.shuffle {
            Some(proof) => {
                let grid = Grid::for_len(n);
                let key = ShuffleKey::new(&pp, grid.n);
                let (ec_in, ed_in) = enc.inputs();
                let encoded = [&ec_in[..], &ed_in, &enc.c_out, &enc.d_out];
                if !proof.verify(&key, &pp, grid, &c_in, &d_in, &d.c_out, &d.d_out, encoded, &round.ctx(STAGE_SHUFFLE, BOTH, 0)) {
                    return Err(Rejection::BadShuffle);
                }
            }
            None => {
                if d.c_out != c_in || d.d_out != d_in {
                    return Err(Rejection::BadShuffle); // decision 27: N = 1 is not shuffled
                }
            }
        }

        // H: everything in the tail expired before theta.
        if let Some(proof) = &p.expiry {
            self.range_key.ensure(e);
            if !verify_expired(&self.range_key, theta as u64, d.tail_dates(), proof, &round.ctx(STAGE_EXPIRY, DATE, 0)) {
                return Err(Rejection::BadExpiry);
            }
        }

        // I: domestic amounts >= 0, and S <= B with this verifier's own B.
        self.range_key.ensure(k + 2);
        if !verify_amounts(&self.range_key, &d.v_dom, &d.v_s, self.limit, &p.amounts, &round.ctx(STAGE_TOTAL, VALUE, 1)) {
            return Err(Rejection::BadAmounts);
        }

        let (signed_c, signed_d) = enc.front(d.e);
        Ok(Approved { round_id: x.round_id, entry, front_c: signed_c.to_vec(), front_d: signed_d.to_vec(), cm_next: d.cm_next })
    }

    // G7, in the order of decision 19b: sign and store the new token, then record
    // the entry atomically, and only then let the token out.
    pub fn finish(&mut self, ns: &mut NullifierSet, ok: Approved) -> Result<StateToken, Rejection> {
        let token = StateToken::issue(&self.sk, self.kid, &ok.front_c, &ok.front_d, ok.cm_next);
        self.pending.insert(ok.round_id, Waiting { token, done: false });
        match ns.insert_if_absent(ok.entry) {
            Insert::AlreadyPresent => {
                self.pending.remove(&ok.round_id);
                Err(Rejection::DoubleSpend)
            }
            Insert::Inserted => {
                self.pending.get_mut(&ok.round_id).expect("stored above").done = true;
                Ok(token)
            }
        }
    }

    // G6 then G7.
    pub fn decide(&mut self, ns: &mut NullifierSet, round_id: &[u8; 32], pkg: &Package) -> Result<StateToken, Rejection> {
        let ok = self.check(ns, round_id, pkg)?;
        self.finish(ns, ok)
    }

    // G9: the approval message was lost; hand out the same token again.
    pub fn resend(&self, round_id: &[u8; 32]) -> Option<StateToken> {
        self.pending.get(round_id).filter(|w| w.done).map(|w| w.token)
    }

    // Decision 26: after a crash, tokens whose entry was never recorded are dropped;
    // the old token is still unspent, so the prover can simply start a new round.
    pub fn restart(&mut self) {
        self.pending.retain(|_, w| w.done);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::operator::Operator;
    use crate::paypay::{PayPay, User};

    const SG: u32 = 1;
    const TH: u32 = 2;
    const ANDI: User = 1;
    const DAY: u32 = 20_741;

    struct World {
        op: Operator,
        sg: Verifier,
        th: Verifier,
        paypay: PayPay,
    }

    fn world() -> World {
        let (sk_sg, sk_th) = (SigningKey::generate(&mut OsRng), SigningKey::generate(&mut OsRng));
        let mut op = Operator::new();
        op.register(SG, sk_sg.verifying_key(), 500_000);
        op.register(TH, sk_th.verifying_key(), 300_000);
        let signed = op.publish();
        let sg = Verifier::new(SG, sk_sg, &signed, &op.public_key()).unwrap();
        let th = Verifier::new(TH, sk_th, &signed, &op.public_key()).unwrap();
        let mut paypay = PayPay::new(&signed, &op.public_key()).unwrap();
        paypay.register(ANDI, b"Andi, passport TR0001234");
        World { op, sg, th, paypay }
    }

    // One full round at verifier `kid` on `day`: ask, respond, decide, accept.
    fn pay(w: &mut World, kid: u32, v: u64, day: u32) -> Result<StateToken, Rejection> {
        let tid = w.paypay.issue_tid(ANDI);
        let verifier = if kid == SG { &mut w.sg } else { &mut w.th };
        let req = verifier.ask(tid, v, day);
        let pkg = w.paypay.respond(&req, day).expect("PayPay answers");
        let token = verifier.decide(&mut w.op.ns, &req.x.round_id, &pkg)?;
        assert!(w.paypay.accept(&req.x.round_id, token));
        Ok(token)
    }

    #[test]
    fn honest_rounds_are_approved() {
        let mut w = world();
        pay(&mut w, SG, 3_200, DAY).unwrap();
        w.paypay.record_domestic(ANDI, 1_250, DAY + 1);
        pay(&mut w, TH, 5_000, DAY + 2).unwrap();
        assert_eq!(w.paypay.list(ANDI).len(), 3);
        assert_eq!(w.op.ns.len(), 2); // Andi's tag, then the first token's nullifier
    }

    #[test]
    fn a_rolled_back_prover_is_caught_by_the_nullifier() {
        // PayPay keeps a copy from before Thailand's round and later shows that older
        // list and its (already spent) token to Singapore.
        let mut w = world();
        pay(&mut w, SG, 3_200, DAY).unwrap();
        let before = w.paypay.clone();
        pay(&mut w, TH, 5_000, DAY + 1).unwrap();

        w.paypay = before;
        assert_eq!(pay(&mut w, SG, 1_000, DAY + 2), Err(Rejection::SpentToken));
    }

    #[test]
    fn re_registering_the_same_person_is_caught_by_the_tag() {
        // A copy of PayPay from before Andi's first payment still has no token for
        // him. Starting him again from an empty history gives the same tag.
        let mut w = world();
        let fresh = w.paypay.clone();
        pay(&mut w, SG, 3_200, DAY).unwrap();

        w.paypay = fresh;
        assert_eq!(pay(&mut w, TH, 1_000, DAY + 1), Err(Rejection::AlreadyRegistered));
    }

    #[test]
    fn one_token_presented_to_two_verifiers_at_once_is_spent_only_once() {
        // Both checks pass, because neither has recorded anything yet. Only the first
        // atomic insert succeeds; the second verifier rejects (G7 step 5).
        let mut w = world();
        pay(&mut w, SG, 3_200, DAY).unwrap();
        let mut twin = w.paypay.clone();

        let (tid1, tid2) = (w.paypay.issue_tid(ANDI), twin.issue_tid(ANDI));
        let req_sg = w.sg.ask(tid1, 1_000, DAY + 1);
        let req_th = w.th.ask(tid2, 1_000, DAY + 1);
        let pkg_sg = w.paypay.respond(&req_sg, DAY + 1).unwrap();
        let pkg_th = twin.respond(&req_th, DAY + 1).unwrap();

        let ok_sg = w.sg.check(&w.op.ns, &req_sg.x.round_id, &pkg_sg).unwrap();
        let ok_th = w.th.check(&w.op.ns, &req_th.x.round_id, &pkg_th).unwrap();
        assert!(w.th.finish(&mut w.op.ns, ok_th).is_ok());
        assert_eq!(w.sg.finish(&mut w.op.ns, ok_sg).err(), Some(Rejection::DoubleSpend));
        assert!(w.sg.resend(&req_sg.x.round_id).is_none());
    }

    #[test]
    fn a_package_answers_only_its_own_round() {
        // Phi for round 1 handed in for round 2: different round_id and x, so a
        // different stmt and ctx, and the proofs no longer fit.
        let mut w = world();
        pay(&mut w, SG, 3_200, DAY).unwrap();
        let tid1 = w.paypay.issue_tid(ANDI);
        let tid2 = w.paypay.issue_tid(ANDI);
        let req1 = w.th.ask(tid1, 1_000, DAY + 1);
        let req2 = w.th.ask(tid2, 1_000, DAY + 1);
        let pkg1 = w.paypay.respond(&req1, DAY + 1).unwrap();
        assert!(w.th.decide(&mut w.op.ns, &req2.x.round_id, &pkg1).is_err());
        // and a round, once decided, cannot be decided again
        assert_eq!(w.th.decide(&mut w.op.ns, &req2.x.round_id, &pkg1).err(), Some(Rejection::UnknownRound));
    }

    #[test]
    fn tampering_with_the_package_is_rejected() {
        // Three edits a prover might try after building an honest package.
        let mut w = world();
        pay(&mut w, SG, 3_200, DAY).unwrap();
        w.paypay.record_domestic(ANDI, 1_250, DAY + 1);

        let try_with = |w: &mut World, edit: &dyn Fn(&mut Package)| {
            let mut copy = w.paypay.clone();
            let tid = copy.issue_tid(ANDI);
            let req = w.th.ask(tid, 1_000, DAY + 2);
            let mut pkg = copy.respond(&req, DAY + 2).unwrap();
            edit(&mut pkg);
            w.th.decide(&mut w.op.ns, &req.x.round_id, &pkg)
        };

        // Leave the old record out of the list (the gap the state token closes).
        let dropped = try_with(&mut w, &|p: &mut Package| {
            if let Start::Token { c_old, d_old, .. } = &mut p.data.start {
                c_old.pop();
                d_old.pop();
            }
        });
        assert_eq!(dropped.err(), Some(Rejection::BadToken));

        // Claim a smaller total.
        let smaller = try_with(&mut w, &|p: &mut Package| p.data.v_s = p.data.c_tx);
        assert!(smaller.is_err());

        // Report one record as expired without a proof for it.
        let no_proof = try_with(&mut w, &|p: &mut Package| p.data.e = 1);
        assert_eq!(no_proof.err(), Some(Rejection::BadShape));

        // Nothing was recorded by any of the rejected rounds.
        assert_eq!(w.op.ns.len(), 1);
    }

    #[test]
    fn a_lost_approval_is_sent_again_and_survives_a_restart() {
        let mut w = world();
        let tid = w.paypay.issue_tid(ANDI);
        let req = w.sg.ask(tid, 3_200, DAY);
        let pkg = w.paypay.respond(&req, DAY).unwrap();
        let token = w.sg.decide(&mut w.op.ns, &req.x.round_id, &pkg).unwrap();

        // The message never reached PayPay. Ask again (G9), even after a restart.
        w.sg.restart();
        assert_eq!(w.sg.resend(&req.x.round_id), Some(token));
        assert!(w.paypay.accept(&req.x.round_id, token));
    }

    #[test]
    fn a_token_whose_entry_was_never_recorded_is_dropped_on_restart() {
        // Crash between storing K' and recording nf (G7 steps 3-4): after a restart
        // the token is gone, and the old one is still unspent.
        let mut w = world();
        pay(&mut w, SG, 3_200, DAY).unwrap();
        let tid = w.paypay.issue_tid(ANDI);
        let req = w.th.ask(tid, 1_000, DAY + 1);
        let pkg = w.paypay.respond(&req, DAY + 1).unwrap();
        let ok = w.th.check(&w.op.ns, &req.x.round_id, &pkg).unwrap();
        let token = StateToken::issue(&w.th.sk, TH, &ok.front_c, &ok.front_d, ok.cm_next);
        w.th.pending.insert(ok.round_id, Waiting { token, done: false }); // step 3 only

        w.th.restart();
        assert!(w.th.resend(&req.x.round_id).is_none());
        assert!(pay(&mut w, TH, 1_000, DAY + 2).is_ok()); // the old token still works
    }

    #[test]
    fn a_verifier_does_not_start_from_a_registry_that_misdescribes_it() {
        let op = Operator::new();
        let stranger = SigningKey::generate(&mut OsRng);
        assert!(Verifier::new(SG, stranger, &op.publish(), &op.public_key()).is_none());
    }
}
