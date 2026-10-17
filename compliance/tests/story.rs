// The story of diagram_urutan.md section 2, end to end, with T = 365 days:
//
//   A1  S$100 in Singapore      15 Jan 2026  (day 20,468)  first payment
//   J1  S$30  domestic, Japan   10 Feb 2026  (day 20,494)  seen by PayPay only
//   T1  S$200 in Thailand        5 Mar 2026  (day 20,517)
//   A2  S$50  in Singapore      20 Jun 2026  (day 20,624)
//   A3  S$40  in Singapore      20 Feb 2027  (day 20,869)  theta = 20,505: A1, J1 expire
//
// Every round runs the real protocol: the verifier asks, PayPay answers with Phi,
// the verifier checks everything and records a nullifier, PayPay keeps the new token.

use compliance::operator::Operator;
use compliance::package::{Package, Start};
use compliance::paypay::{PayPay, User};
use compliance::verifier::Verifier;
use ed25519_dalek::SigningKey;
use ibc::commitment::Commitment;
use rand_core::OsRng;

const SINGAPORE: u32 = 1;
const THAILAND: u32 = 2;
const ANDI: User = 1;

struct World {
    op: Operator,
    alipay: Verifier,
    thailand: Verifier,
    paypay: PayPay,
}

fn world() -> World {
    let (sk_sg, sk_th) = (SigningKey::generate(&mut OsRng), SigningKey::generate(&mut OsRng));
    let mut op = Operator::new();
    op.register(SINGAPORE, sk_sg.verifying_key(), 500_000); // B = S$5,000
    op.register(THAILAND, sk_th.verifying_key(), 300_000);
    let signed = op.publish();
    let alipay = Verifier::new(SINGAPORE, sk_sg, &signed, &op.public_key()).unwrap();
    let thailand = Verifier::new(THAILAND, sk_th, &signed, &op.public_key()).unwrap();
    let mut paypay = PayPay::new(&signed, &op.public_key()).unwrap();
    paypay.register(ANDI, b"Andi, passport TR0001234");
    World { op, alipay, thailand, paypay }
}

// One cross-border payment; returns the package the verifier saw.
fn pay(w: &mut World, at: u32, cents: u64, day: u32) -> Package {
    let tid = w.paypay.issue_tid(ANDI);
    let verifier = if at == SINGAPORE { &mut w.alipay } else { &mut w.thailand };
    let req = verifier.ask(tid, cents, day);
    let pkg = w.paypay.respond(&req, day).expect("Andi stays under the limit");
    let token = verifier.decide(&mut w.op.ns, &req.x.round_id, &pkg).expect("an honest round is approved");
    assert!(w.paypay.accept(&req.x.round_id, token));
    pkg
}

fn days(w: &World) -> Vec<u32> {
    let mut d: Vec<u32> = w.paypay.list(ANDI).iter().map(|r| r.t).collect();
    d.sort();
    d
}

#[test]
fn singapore_japan_thailand_singapore_and_a_year_later() {
    let mut w = world();

    // January, Singapore: the first payment registers Andi's tag.
    let jan = pay(&mut w, SINGAPORE, 10_000, 20_468);
    assert!(matches!(jan.data.start, Start::First { .. }));
    assert_eq!((days(&w), w.op.ns.len()), (vec![20_468], 1));

    // February, Japan: a domestic payment. No verifier is involved.
    w.paypay.record_domestic(ANDI, 3_000, 20_494);

    // March, Thailand: Singapore's token is spent; J1 joins the list.
    let mar = pay(&mut w, THAILAND, 20_000, 20_517);
    assert_eq!((mar.data.c_old().len(), mar.data.c_dom.len(), mar.data.e), (1, 1, 0));
    assert_eq!((days(&w), w.op.ns.len()), (vec![20_468, 20_494, 20_517], 2));

    // June, Singapore again. Alipay+ receives three old commitments, and none of them
    // is the A1 commitment it saw in January: the shuffles re-randomised them all.
    let jun = pay(&mut w, SINGAPORE, 5_000, 20_624);
    let a1_seen_in_january: Commitment = jan.data.c_tx;
    assert_eq!(jun.data.c_old().len(), 3);
    assert!(!jun.data.c_old().contains(&a1_seen_in_january));
    assert_eq!(w.op.ns.len(), 3);

    // February next year, Singapore: theta = 20,505, so A1 and J1 have expired.
    // Alipay+ learns that two records were dropped, not which ones.
    let feb = pay(&mut w, SINGAPORE, 4_000, 20_869);
    assert_eq!(feb.data.e, 2);
    assert_eq!(days(&w), vec![20_517, 20_624, 20_869]);
    assert_eq!(w.op.ns.len(), 4); // one tag and three spent tokens
}

#[test]
fn the_window_moves_one_day_at_a_time() {
    // The window is the last 365 days, today included (decision 32). A record from
    // day d counts on days d ..= d + 364 and is dropped on day d + 365.
    let mut w = world();
    pay(&mut w, SINGAPORE, 10_000, 20_000);

    let kept = pay(&mut w, THAILAND, 1_000, 20_364);
    assert_eq!(kept.data.e, 0);

    let dropped = pay(&mut w, THAILAND, 1_000, 20_365);
    assert_eq!(dropped.data.e, 1);
    assert_eq!(days(&w), vec![20_364, 20_365]);
}

#[test]
fn a_payment_that_would_cross_the_limit_is_refused_by_paypay() {
    // Thailand's B is S$3,000. S$2,000 earlier this year plus S$1,500 now is too much,
    // and PayPay refuses before opening anything (G4 step 7).
    let mut w = world();
    pay(&mut w, THAILAND, 200_000, 20_500);
    let tid = w.paypay.issue_tid(ANDI);
    let req = w.thailand.ask(tid, 150_000, 20_600);
    assert!(w.paypay.respond(&req, 20_600).is_err());

    // A year later the old payment no longer counts, and the same amount goes through.
    pay(&mut w, THAILAND, 150_000, 20_900);
}
