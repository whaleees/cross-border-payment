use std::collections::HashMap;

use curve25519_dalek::Scalar;
use curve25519_dalek::ristretto::CompressedRistretto;
use ed25519_dalek::VerifyingKey;
use ibc::commitment::{Commitment, Opening, commit, random_blinding};
use ibc::fulleq::FullEqProof;
use ibc::mideq::MIDEqProof;
use ibc::params::{hash_identity, value_to_scalar};
use ibc::txver::TxVerProof;
use ibc::veq::VEqProof;
use rand_core::{OsRng, RngCore};

use crate::ctx::{BOTH, DATE, Round, STAGE_DOMESTIC, STAGE_EXPIRY, STAGE_MIDEQ, STAGE_NEW_PAIR, STAGE_SHUFFLE, STAGE_TAG, STAGE_TOTAL, VALUE};
use crate::operator::{Registry, SignedRegistry};
use crate::package::{Package, Proofs, RoundData, Start, statement};
use crate::params::{Params, ShuffleKey, window_start};
use crate::range::{Opened, RangeKey, prove_amounts, prove_expired};
use crate::request::{Request, SignedRequest};
use crate::shuffle::{Grid, ShuffleProof};
use crate::state_token::{StateToken, fresh_preimage, nullifier_commitment};
use crate::tag::{TagProof, tag};

// The prover's side of one round (alur_gabungan.md G1-G5, G8, and G7 steps 7-10).
// PayPay holds every opening; the verifier only ever sees commitments and proofs.

pub type User = u64;

// One transaction pair (c, d) and its opening.
#[derive(Clone, Copy, Debug)]
pub struct Record {
    pub c: Commitment,
    pub d: Commitment,
    pub v: u64, // amount, SGD cents
    pub t: u32, // UTC day number
    pub r: Scalar,
    pub s: Scalar,
}

impl Record {
    fn opening(&self, id: Scalar) -> Opening {
        Opening { id, val: value_to_scalar(self.v), blinding: self.r }
    }
}

#[derive(Clone)]
struct Account {
    id: Scalar,
    list: Vec<Record>,                     // last front, in the signed order
    token: Option<(StateToken, [u8; 32])>, // last state token and its rho
    domestic: Vec<Record>,                 // domestic payments not yet in the list
}

#[derive(Clone)]
struct Tid {
    user: User,
    s: Scalar,
    used: bool,
}

// Kept from sending Phi until the verifier's token arrives.
#[derive(Clone)]
struct Pending {
    user: User,
    kid: u32,
    front: Vec<Record>,
    front_c: Vec<CompressedRistretto>, // the front, compressed: what K' must sign
    front_d: Vec<CompressedRistretto>,
    rho_next: [u8; 32],
    cm_next: [u8; 32],
    domestic_used: usize,
}

// Why a request got no package. The verifier is only told "refused" (G3, G4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    UnknownVerifier,
    BadSignature,
    WrongLimit,
    WrongPeriod,
    WrongDate,
    UnknownTid,
    UsedTid,
    OverLimit,
}

// Clone lets a test keep an old copy of PayPay and replay it: the rollback and
// re-registration attacks the nullifier set exists for.
#[derive(Clone)]
pub struct PayPay {
    k_p: [u8; 32],
    params: Params,
    registry: Registry,
    range_key: RangeKey,
    accounts: HashMap<User, Account>,
    tids: HashMap<[u8; 32], Tid>,
    pending: HashMap<[u8; 32], Pending>,
}

fn shuffled(mut v: Vec<usize>) -> Vec<usize> {
    for i in (1..v.len()).rev() {
        v.swap(i, (OsRng.next_u64() % (i as u64 + 1)) as usize);
    }
    v
}

impl PayPay {
    // G0 steps 12-13: no registry the operator did not sign.
    pub fn new(signed: &SignedRegistry, operator_pk: &VerifyingKey) -> Option<Self> {
        if !signed.verify(operator_pk) {
            return None;
        }
        let mut k_p = [0u8; 32];
        OsRng.fill_bytes(&mut k_p);
        let params = Params::setup();
        Some(PayPay {
            k_p,
            params,
            registry: signed.registry.clone(),
            range_key: RangeKey::new(&params.pp, 4),
            accounts: HashMap::new(),
            tids: HashMap::new(),
            pending: HashMap::new(),
        })
    }

    // G0 step 14: id = hash_identity(k_P || KYC data), so nobody else can compute it.
    pub fn register(&mut self, user: User, kyc: &[u8]) {
        let id = hash_identity(&[&self.k_p[..], kyc].concat());
        self.accounts.insert(user, Account { id, list: Vec::new(), token: None, domestic: Vec::new() });
    }

    // G1: a domestic payment, committed now, inserted at the next cross-border round.
    pub fn record_domestic(&mut self, user: User, v: u64, t: u32) {
        let pp = self.params.pp;
        let acct = self.accounts.get_mut(&user).expect("registered user");
        let (r, s) = (random_blinding(), random_blinding());
        let c = commit(&pp, &Opening { id: acct.id, val: value_to_scalar(v), blinding: r });
        let d = Commitment(Scalar::from(t) * pp.g_val + s * pp.g_ran);
        acct.domestic.push(Record { c, d, v, t, r, s });
    }

    // G2: a fresh tid = id*g_iden + s*g_ran for every payment.
    pub fn issue_tid(&mut self, user: User) -> Commitment {
        let id = self.accounts[&user].id;
        let s = random_blinding();
        let tid = commit(&self.params.pp, &Opening { id, val: Scalar::ZERO, blinding: s });
        self.tids.insert(tid.to_bytes(), Tid { user, s, used: false });
        tid
    }

    pub fn list(&self, user: User) -> &[Record] {
        &self.accounts[&user].list
    }

    // G3 steps 5-11, G4, G5 (G8 for a first payment). Today is PayPay's own clock.
    pub fn respond(&mut self, req: &SignedRequest, today: u32) -> Result<Package, Refusal> {
        let x = req.x;

        // G3 5-9: who asks, and is the question the agreed one?
        let entry = *self.registry.get(x.kid).ok_or(Refusal::UnknownVerifier)?;
        if !req.verify(&entry.pk) {
            return Err(Refusal::BadSignature);
        }
        if x.limit != entry.limit {
            return Err(Refusal::WrongLimit);
        }
        if x.period != self.registry.period_days {
            return Err(Refusal::WrongPeriod);
        }
        if !(x.t_now == today || x.t_now + 1 == today) {
            return Err(Refusal::WrongDate);
        }
        let tid = self.tids.get_mut(&x.tid.to_bytes()).ok_or(Refusal::UnknownTid)?;
        if tid.used {
            return Err(Refusal::UsedTid);
        }
        tid.used = true; // G3 10: one request per tid, whatever happens next
        let (user, s_tid) = (tid.user, tid.s);

        // G4: what is still inside the window, and would this payment fit under B?
        let theta = window_start(x.t_now, x.period);
        let acct = self.accounts.get_mut(&user).expect("a tid always belongs to a user");
        acct.domestic.retain(|r| r.t >= theta); // expired before being reported: dropped
        let (id, old, domestic, token) = (acct.id, acct.list.clone(), acct.domestic.clone(), acct.token);

        let live = |r: &Record| r.t >= theta;
        let e = old.iter().filter(|r| !live(r)).count();
        let total = old.iter().filter(|r| live(r)).chain(&domestic).map(|r| r.v).try_fold(x.v, u64::checked_add);
        let total = match total {
            Some(t) if t <= x.limit => t,
            _ => return Err(Refusal::OverLimit), // G4 7: rho stays closed
        };

        Ok(self.build_package(&req.x, user, id, s_tid, theta, old, domestic, token, e, total))
    }

    // G5 (and G8 when there is no token yet).
    #[allow(clippy::too_many_arguments)]
    fn build_package(
        &mut self,
        x: &Request,
        user: User,
        id: Scalar,
        s_tid: Scalar,
        theta: u32,
        old: Vec<Record>,
        domestic: Vec<Record>,
        token: Option<(StateToken, [u8; 32])>,
        e: usize,
        total: u64,
    ) -> Package {
        let pp = self.params.pp;

        // A: this payment's pair. d_tx has a random blinding (decision 21).
        let (r_tx, s_tx) = (random_blinding(), random_blinding());
        let c_tx = commit(&pp, &Opening { id, val: value_to_scalar(x.v), blinding: r_tx });
        let d_tx = Commitment(Scalar::from(x.t_now) * pp.g_val + s_tx * pp.g_ran);
        let d_ref = Commitment(Scalar::from(x.t_now) * pp.g_val);
        let tx = Record { c: c_tx, d: d_tx, v: x.v, t: x.t_now, r: r_tx, s: s_tx };

        // B: inputs = old || domestic || this payment.
        let inputs: Vec<Record> = old.iter().chain(&domestic).copied().chain([tx]).collect();
        let n = inputs.len();

        // C: expired inputs to the tail, everything else to the front, random order in each.
        let (front_idx, tail_idx): (Vec<usize>, Vec<usize>) = (0..n).partition(|&i| inputs[i].t >= theta);
        debug_assert_eq!(tail_idx.len(), e);
        let perm: Vec<usize> = shuffled(front_idx).into_iter().chain(shuffled(tail_idx)).collect();
        let rerand = |_| if n == 1 { Scalar::ZERO } else { random_blinding() };
        let delta: Vec<Scalar> = (0..n).map(rerand).collect();
        let eta: Vec<Scalar> = (0..n).map(rerand).collect();
        let outputs: Vec<Record> = (0..n)
            .map(|j| {
                let src = inputs[perm[j]];
                Record {
                    c: Commitment(src.c.0 + delta[j] * pp.g_ran),
                    d: Commitment(src.d.0 + eta[j] * pp.g_ran),
                    r: src.r + delta[j],
                    s: src.s + eta[j],
                    ..src
                }
            })
            .collect();
        let f = n - e;

        // D: two-basis copies for the range proofs.
        let gammas: Vec<Scalar> = domestic.iter().map(|_| random_blinding()).collect();
        let v_dom: Vec<Commitment> = domestic
            .iter()
            .zip(&gammas)
            .map(|(r, g)| commit(&pp, &Opening { id: Scalar::ZERO, val: value_to_scalar(r.v), blinding: *g }))
            .collect();
        let gamma_s = random_blinding();
        let v_s = commit(&pp, &Opening { id: Scalar::ZERO, val: value_to_scalar(total), blinding: gamma_s });

        // E: the next token's hidden nullifier.
        let rho_next = fresh_preimage();
        let cm_next = nullifier_commitment(&rho_next);

        // F: the round's statement.
        let start = match token {
            Some((token, rho)) => Start::Token {
                token,
                rho,
                c_old: old.iter().map(|r| r.c).collect(),
                d_old: old.iter().map(|r| r.d).collect(),
            },
            None => Start::First { tag: tag(&self.params, &id) },
        };
        let data = RoundData {
            start,
            cm_next,
            c_dom: domestic.iter().map(|r| r.c).collect(),
            d_dom: domestic.iter().map(|r| r.d).collect(),
            v_dom,
            c_tx,
            d_tx,
            c_out: outputs.iter().map(|r| r.c).collect(),
            d_out: outputs.iter().map(|r| r.d).collect(),
            e: e as u32,
            v_s,
        };
        let enc = data.encode(); // every list compressed once (decision 34)
        let round = Round { round_id: x.round_id, stmt: statement(x, &data, &enc) };

        // G: the proofs.
        let o_tid = Opening { id, val: Scalar::ZERO, blinding: s_tid };
        let tag_proof = match &data.start {
            Start::First { tag } => Some(TagProof::prove(&self.params, &x.tid, tag, &o_tid, &round.ctx(STAGE_TAG, VALUE, 0))),
            Start::Token { .. } => None,
        };

        let mideq = (!old.is_empty() || !domestic.is_empty()).then(|| {
            let cs: Vec<Commitment> = [x.tid].into_iter().chain(old.iter().chain(&domestic).map(|r| r.c)).collect();
            let os: Vec<Opening> = [o_tid].into_iter().chain(old.iter().chain(&domestic).map(|r| r.opening(id))).collect();
            MIDEqProof::prove(&pp, &cs, &os, &round.ctx(STAGE_MIDEQ, VALUE, 0))
        });

        let txver = TxVerProof::prove(&pp, &x.tid, &c_tx, value_to_scalar(x.v), &o_tid, &tx.opening(id), &round.ctx(STAGE_NEW_PAIR, VALUE, 0));
        let date = |blinding| Opening { id: Scalar::ZERO, val: Scalar::from(x.t_now), blinding };
        let fulleq = FullEqProof::prove(&pp, &d_tx, &d_ref, &date(s_tx), &date(Scalar::ZERO), &round.ctx(STAGE_NEW_PAIR, DATE, 0));

        let domestic_proofs = domestic
            .iter()
            .zip(&gammas)
            .zip(&data.v_dom)
            .enumerate()
            .map(|(j, ((r, g), v))| {
                let copy = Opening { id: Scalar::ZERO, val: value_to_scalar(r.v), blinding: *g };
                VEqProof::prove(&pp, &r.c, v, &r.opening(id), &copy, &round.ctx(STAGE_DOMESTIC, VALUE, j as u32 + 1))
            })
            .collect();

        let front = &outputs[..f];
        let c_sum = front.iter().skip(1).fold(front[0].c, |acc, r| acc + r.c);
        let o_sum = Opening {
            id: Scalar::from(f as u64) * id,
            val: value_to_scalar(total),
            blinding: front.iter().map(|r| r.r).sum(),
        };
        let o_vs = Opening { id: Scalar::ZERO, val: value_to_scalar(total), blinding: gamma_s };
        let sum = VEqProof::prove(&pp, &c_sum, &v_s, &o_sum, &o_vs, &round.ctx(STAGE_TOTAL, VALUE, 0));

        let shuffle = (n >= 2).then(|| {
            let grid = Grid::for_len(n);
            let key = ShuffleKey::new(&pp, grid.n);
            let (c_in, d_in) = data.inputs();
            let (ec_in, ed_in) = enc.inputs();
            let encoded = [&ec_in[..], &ed_in, &enc.c_out, &enc.d_out];
            ShuffleProof::prove(&key, &pp, grid, &c_in, &d_in, &data.c_out, &data.d_out, encoded, &perm, &delta, &eta, &round.ctx(STAGE_SHUFFLE, BOTH, 0))
        });

        let expiry = (e > 0).then(|| {
            self.range_key.ensure(e);
            let tail: Vec<Opened> = outputs[f..].iter().map(|r| Opened { v: r.t as u64, blinding: r.s }).collect();
            prove_expired(&self.range_key, theta as u64, &tail, &round.ctx(STAGE_EXPIRY, DATE, 0)).expect("every tail date is expired")
        });

        self.range_key.ensure(domestic.len() + 2);
        let dom_open: Vec<Opened> = domestic.iter().zip(&gammas).map(|(r, g)| Opened { v: r.v, blinding: *g }).collect();
        let amounts = prove_amounts(&self.range_key, &dom_open, &Opened { v: total, blinding: gamma_s }, x.limit, &round.ctx(STAGE_TOTAL, VALUE, 1))
            .expect("S <= B was checked in G4");

        let (front_c, front_d) = enc.front(data.e);
        self.pending.insert(
            x.round_id,
            Pending {
                user,
                kid: x.kid,
                front: front.to_vec(),
                front_c: front_c.to_vec(),
                front_d: front_d.to_vec(),
                rho_next,
                cm_next,
                domestic_used: domestic.len(),
            },
        );

        Package {
            data,
            proofs: Proofs { tag: tag_proof, mideq, txver, fulleq, domestic: domestic_proofs, sum, shuffle, expiry, amounts },
        }
    }

    // G7 steps 7-10: the verifier approved and sent K'. Keep it only if it really is
    // the right verifier's signature over the front PayPay holds and over cm'.
    pub fn accept(&mut self, round_id: &[u8; 32], token: StateToken) -> bool {
        let Some(p) = self.pending.get(round_id) else { return false };
        let Some(entry) = self.registry.get(p.kid) else { return false };
        if token.kid != p.kid || token.cm != p.cm_next || !token.verify(&entry.pk, &p.front_c, &p.front_d) {
            return false;
        }

        let p = self.pending.remove(round_id).expect("checked above");
        let acct = self.accounts.get_mut(&p.user).expect("registered user");
        acct.list = p.front; // the tail is dropped here
        acct.token = Some((token, p.rho_next));
        acct.domestic.drain(..p.domestic_used);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::operator::Operator;
    use crate::range::{verify_amounts, verify_expired};
    use ed25519_dalek::SigningKey;

    const SG: u32 = 1;
    const TH: u32 = 2;
    const SG_LIMIT: u64 = 500_000; // S$5,000
    const TH_LIMIT: u64 = 300_000;
    const ANDI: User = 1;
    const TODAY: u32 = 20_741; // 15 Oct 2026

    struct World {
        sg: SigningKey,
        th: SigningKey,
        paypay: PayPay,
    }

    fn world() -> World {
        let (sg, th) = (SigningKey::generate(&mut OsRng), SigningKey::generate(&mut OsRng));
        let mut op = Operator::new();
        op.register(SG, sg.verifying_key(), SG_LIMIT);
        op.register(TH, th.verifying_key(), TH_LIMIT);
        let mut paypay = PayPay::new(&op.publish(), &op.public_key()).unwrap();
        paypay.register(ANDI, b"Andi, passport TR0001234");
        World { sg, th, paypay }
    }

    fn round_id() -> [u8; 32] {
        let mut r = [0u8; 32];
        OsRng.fill_bytes(&mut r);
        r
    }

    // A request as verifier kid would send it.
    fn ask(tid: Commitment, v: u64, t_now: u32, kid: u32, limit: u64, sk: &SigningKey) -> SignedRequest {
        Request { tid, v, t_now, period: 365, limit, round_id: round_id(), kid }.sign(sk)
    }

    // Plays the verifier's G7 steps 1-2: the verifier that asked signs the front with cm'.
    fn approve(w: &mut World, req: &SignedRequest, pkg: &Package) -> bool {
        let sk = if req.x.kid == SG { &w.sg } else { &w.th };
        let enc = pkg.data.encode();
        let (cs, ds) = enc.front(pkg.data.e);
        let token = StateToken::issue(sk, req.x.kid, cs, ds, pkg.data.cm_next);
        w.paypay.accept(&req.x.round_id, token)
    }

    #[test]
    fn requests_failing_any_check_are_refused() {
        let mut w = world();
        let tid = w.paypay.issue_tid(ANDI);
        let stranger = SigningKey::generate(&mut OsRng);
        let cases = [
            (ask(tid, 1_000, TODAY, 9, SG_LIMIT, &w.sg), Refusal::UnknownVerifier),
            (ask(tid, 1_000, TODAY, SG, SG_LIMIT, &stranger), Refusal::BadSignature), // e.g. the merchant
            (ask(tid, 1_000, TODAY, SG, 1_000, &w.sg), Refusal::WrongLimit),          // probing with a chosen B
            (ask(tid, 1_000, TODAY + 1, SG, SG_LIMIT, &w.sg), Refusal::WrongDate),
            (ask(tid, 1_000, TODAY - 2, SG, SG_LIMIT, &w.sg), Refusal::WrongDate),
            (ask(Commitment(tid.0 + tid.0), 1_000, TODAY, SG, SG_LIMIT, &w.sg), Refusal::UnknownTid),
        ];
        for (req, why) in cases {
            assert_eq!(w.paypay.respond(&req, TODAY).err(), Some(why));
        }
        // T = 30 instead of 365, to move theta.
        let shorter = Request { tid, v: 1_000, t_now: TODAY, period: 30, limit: SG_LIMIT, round_id: round_id(), kid: SG };
        assert_eq!(w.paypay.respond(&shorter.sign(&w.sg), TODAY).err(), Some(Refusal::WrongPeriod));
    }

    #[test]
    fn today_and_yesterday_are_accepted_and_a_tid_works_once() {
        let mut w = world();
        let tid = w.paypay.issue_tid(ANDI);
        assert!(w.paypay.respond(&ask(tid, 1_000, TODAY - 1, SG, SG_LIMIT, &w.sg), TODAY).is_ok());
        let again = ask(tid, 1_000, TODAY, SG, SG_LIMIT, &w.sg);
        assert_eq!(w.paypay.respond(&again, TODAY).err(), Some(Refusal::UsedTid));
    }

    #[test]
    fn over_the_limit_is_refused_and_nothing_is_sent() {
        // G4 step 7: no package, so no rho, and the tid is spent all the same.
        let mut w = world();
        let tid = w.paypay.issue_tid(ANDI);
        let req = ask(tid, SG_LIMIT + 1, TODAY, SG, SG_LIMIT, &w.sg);
        assert_eq!(w.paypay.respond(&req, TODAY).err(), Some(Refusal::OverLimit));
        assert!(w.paypay.pending.is_empty());
        assert_eq!(w.paypay.respond(&req, TODAY).err(), Some(Refusal::UsedTid));
    }

    #[test]
    fn the_first_payment_carries_a_tag_and_no_shuffle() {
        // No old list, no domestic records: N = 1, so the front is just (c_tx, d_tx).
        let mut w = world();
        let tid = w.paypay.issue_tid(ANDI);
        let req = ask(tid, 3_200, TODAY, SG, SG_LIMIT, &w.sg);
        let pkg = w.paypay.respond(&req, TODAY).unwrap();

        let Start::First { tag } = &pkg.data.start else { panic!("first payment") };
        assert!(pkg.proofs.mideq.is_none() && pkg.proofs.shuffle.is_none() && pkg.proofs.expiry.is_none());
        assert_eq!(pkg.data.c_out, vec![pkg.data.c_tx]);

        let round = Round { round_id: req.x.round_id, stmt: statement(&req.x, &pkg.data, &pkg.data.encode()) };
        let proof: &TagProof = pkg.proofs.tag.as_ref().unwrap();
        assert!(proof.verify(&w.paypay.params, &tid, tag, &round.ctx(STAGE_TAG, VALUE, 0)));
    }

    #[test]
    fn domestic_records_still_in_the_window_join_the_first_payment() {
        // Keputusan 17f: every domestic record inside T joins; one from 400 days ago
        // expired before it was ever reported and is dropped.
        let mut w = world();
        w.paypay.record_domestic(ANDI, 900, TODAY - 400);
        w.paypay.record_domestic(ANDI, 1_250, TODAY - 10);
        w.paypay.record_domestic(ANDI, 300, TODAY - 3);
        let tid = w.paypay.issue_tid(ANDI);
        let req = ask(tid, 3_200, TODAY, SG, SG_LIMIT, &w.sg);
        let pkg = w.paypay.respond(&req, TODAY).unwrap();

        assert_eq!((pkg.data.c_dom.len(), pkg.data.n(), pkg.data.e), (2, 3, 0));
        assert!(pkg.proofs.mideq.is_some() && pkg.proofs.shuffle.is_some());

        // The amounts proof covers both domestic amounts and S = 4,750.
        let round = Round { round_id: req.x.round_id, stmt: statement(&req.x, &pkg.data, &pkg.data.encode()) };
        let key = RangeKey::new(&w.paypay.params.pp, 4);
        assert!(verify_amounts(&key, &pkg.data.v_dom, &pkg.data.v_s, SG_LIMIT, &pkg.proofs.amounts, &round.ctx(STAGE_TOTAL, VALUE, 1)));

        assert!(approve(&mut w, &req, &pkg));
        assert_eq!(w.paypay.list(ANDI).len(), 3);
        assert!(w.paypay.accounts[&ANDI].domestic.is_empty());
    }

    #[test]
    fn a_later_payment_spends_the_token_and_drops_what_expired() {
        // Day 20,000 in Singapore, a domestic payment on day 20,100, then Thailand on
        // day 20,400: theta = 20,036, so the Singapore payment has expired (e = 1).
        let mut w = world();
        let tid = w.paypay.issue_tid(ANDI);
        let req1 = ask(tid, 3_200, 20_000, SG, SG_LIMIT, &w.sg);
        let pkg1 = w.paypay.respond(&req1, 20_000).unwrap();
        assert!(approve(&mut w, &req1, &pkg1));

        w.paypay.record_domestic(ANDI, 1_250, 20_100);
        let tid = w.paypay.issue_tid(ANDI);
        let req2 = ask(tid, 5_000, 20_400, TH, TH_LIMIT, &w.th);
        let pkg2 = w.paypay.respond(&req2, 20_400).unwrap();

        let Start::Token { token, rho, .. } = &pkg2.data.start else { panic!("second payment") };
        let enc = pkg2.data.encode();
        assert!(token.verify(&w.sg.verifying_key(), &enc.c_old, &enc.d_old)); // the list Singapore signed
        assert!(token.open(rho).is_some()); // rho opens cm, giving the nullifier
        assert_eq!((pkg2.data.n(), pkg2.data.e), (3, 1));

        let round = Round { round_id: req2.x.round_id, stmt: statement(&req2.x, &pkg2.data, &enc) };
        let pp = w.paypay.params.pp;

        // The shuffle and the tail's expiry check out against the data in Phi.
        let grid = Grid::for_len(3);
        let (c_in, d_in) = pkg2.data.inputs();
        let (ec_in, ed_in) = enc.inputs();
        let encoded = [&ec_in[..], &ed_in, &enc.c_out, &enc.d_out];
        let shuffle = pkg2.proofs.shuffle.as_ref().unwrap();
        assert!(shuffle.verify(&ShuffleKey::new(&pp, grid.n), &pp, grid, &c_in, &d_in, &pkg2.data.c_out, &pkg2.data.d_out, encoded, &round.ctx(STAGE_SHUFFLE, BOTH, 0)));
        let key = RangeKey::new(&pp, 4);
        let expiry = pkg2.proofs.expiry.as_ref().unwrap();
        assert!(verify_expired(&key, 20_036, pkg2.data.tail_dates(), expiry, &round.ctx(STAGE_EXPIRY, DATE, 0)));

        // After approval the list is the front: the domestic record and this payment.
        assert!(approve(&mut w, &req2, &pkg2));
        let days: Vec<u32> = { let mut d: Vec<u32> = w.paypay.list(ANDI).iter().map(|r| r.t).collect(); d.sort(); d };
        assert_eq!(days, vec![20_100, 20_400]);
    }

    #[test]
    fn a_token_for_anything_else_is_not_kept() {
        // Wrong signer, wrong cm, or a different list: PayPay keeps waiting.
        let mut w = world();
        let tid = w.paypay.issue_tid(ANDI);
        let req = ask(tid, 3_200, TODAY, SG, SG_LIMIT, &w.sg);
        let pkg = w.paypay.respond(&req, TODAY).unwrap();
        let enc = pkg.data.encode();
        let (cs, ds) = enc.front(pkg.data.e);

        let by_thailand = StateToken::issue(&w.th, SG, cs, ds, pkg.data.cm_next);
        let wrong_cm = StateToken::issue(&w.sg, SG, cs, ds, [0; 32]);
        let other_list = StateToken::issue(&w.sg, SG, &[enc.c_tx, enc.c_tx], &[enc.d_tx, enc.d_tx], pkg.data.cm_next);
        for bad in [by_thailand, wrong_cm, other_list] {
            assert!(!w.paypay.accept(&req.x.round_id, bad));
        }
        assert!(w.paypay.list(ANDI).is_empty());
        assert!(approve(&mut w, &req, &pkg));
    }
}
