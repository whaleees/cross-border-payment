// One round at every level of decision 35, side by side, ending in one table:
//
//   cargo run --release --example compare -- 1000 10
//
// The arguments are N (default 1,000) and runs per level (default 10). The runs of
// the levels are interleaved, so if the laptop slows down halfway, every level slows
// down alike. Each run starts from the same history: a fresh copy of PayPay and of
// the verifier, one request, PayPay answering (timed), the verifier deciding (timed).
//
// The history is built once per N and saved to target/compare-history-N.bin; later
// runs at that N load it in seconds. Add --fresh to build it again.

use std::path::PathBuf;
use std::time::Instant;

use compliance::level::Level;
use compliance::operator::{Entry, NullifierSet, Operator};
use compliance::paypay::{PayPay, Record, SavedAccount, User};
use compliance::shuffle::Grid;
use compliance::state_token::StateToken;
use compliance::verifier::Verifier;
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::{RistrettoPoint, Scalar};
use ed25519_dalek::{Signature, SigningKey};
use ibc::commitment::Commitment;
use rand_core::OsRng;

const ANDI: User = 1;
const DAY: u32 = 20_741;
const LIMIT: u64 = u64::MAX / 4; // a limit nobody reaches here
const FORMAT: &[u8; 8] = b"cmphist1";

// Operator, verifier and PayPay on given keys: the same keys give the same registry,
// so a saved state token still verifies.
fn parties(op_sk: &SigningKey, v_sk: &SigningKey) -> (Operator, Verifier, PayPay) {
    let mut op = Operator::with_key(op_sk.clone());
    op.register(1, v_sk.verifying_key(), LIMIT);
    let signed = op.publish();
    let verifier = Verifier::new(1, v_sk.clone(), &signed, &op.public_key()).unwrap();
    let paypay = PayPay::new(&signed, &op.public_key()).unwrap();
    (op, verifier, paypay)
}

// Andi with n - 1 records and a state token. Built by payments that each bring in at
// most 999 domestic records, so that no single range proof covers thousands of
// amounts (one payment would do up to n = 1,000, as in benches/scaling.rs).
fn build(n: usize, op_sk: &SigningKey, v_sk: &SigningKey) -> (PayPay, Verifier, NullifierSet) {
    let (mut op, mut verifier, mut paypay) = parties(op_sk, v_sk);
    paypay.register(ANDI, b"Andi, passport TR0001234");
    let mut missing = n - 1;
    while missing > 0 {
        let domestic = (missing - 1).min(999);
        for _ in 0..domestic {
            paypay.record_domestic(ANDI, 100, DAY - 1);
        }
        let tid = paypay.issue_tid(ANDI);
        let req = verifier.ask(tid, 100, DAY - 1);
        let pkg = paypay.respond(&req, DAY - 1).unwrap();
        let token = verifier.decide(&mut op.ns, &req.x.round_id, &pkg).unwrap();
        assert!(paypay.accept(&req.x.round_id, token));
        missing -= domestic + 1;
        print!("\rBuilding Andi's history: {} of {} records", n - 1 - missing, n - 1);
        std::io::Write::flush(&mut std::io::stdout()).ok();
    }
    println!();
    (paypay, verifier, op.ns)
}

// The file: FORMAT, n, the two secret keys, Andi's account, the nullifier set.
fn save(path: &PathBuf, n: usize, op_sk: &SigningKey, v_sk: &SigningKey, paypay: &PayPay, ns: &NullifierSet) {
    let acct = paypay.export_account(ANDI).expect("an approved history");
    let mut out = Vec::new();
    out.extend(FORMAT);
    out.extend((n as u64).to_le_bytes());
    out.extend(op_sk.to_bytes());
    out.extend(v_sk.to_bytes());
    out.extend(acct.id.to_bytes());
    out.extend(acct.token.kid.to_le_bytes());
    out.extend(acct.token.cm);
    out.extend(acct.token.sig.to_bytes());
    out.extend(acct.rho);
    out.extend((acct.list.len() as u64).to_le_bytes());
    for r in &acct.list {
        out.extend(r.c.0.compress().to_bytes());
        out.extend(r.d.0.compress().to_bytes());
        out.extend(r.v.to_le_bytes());
        out.extend(r.t.to_le_bytes());
        out.extend(r.r.to_bytes());
        out.extend(r.s.to_bytes());
    }
    let entries: Vec<&Entry> = ns.entries().collect();
    out.extend((entries.len() as u64).to_le_bytes());
    for e in entries {
        let (kind, bytes) = match e {
            Entry::Nullifier(b) => (0u8, b),
            Entry::Tag(b) => (1u8, b),
        };
        out.push(kind);
        out.extend(bytes);
    }
    std::fs::write(path, out).expect("write the history file");
}

struct Reader<'a>(&'a [u8]);

impl Reader<'_> {
    fn take<const L: usize>(&mut self) -> Option<[u8; L]> {
        let (head, rest) = self.0.split_at_checked(L)?;
        self.0 = rest;
        head.try_into().ok()
    }
    fn u64(&mut self) -> Option<u64> {
        self.take().map(u64::from_le_bytes)
    }
    fn point(&mut self) -> Option<RistrettoPoint> {
        CompressedRistretto(self.take()?).decompress()
    }
    fn scalar(&mut self) -> Option<Scalar> {
        Scalar::from_canonical_bytes(self.take()?).into()
    }
}

fn load(path: &PathBuf, n: usize) -> Option<(PayPay, Verifier, NullifierSet)> {
    let bytes = std::fs::read(path).ok()?;
    let mut rd = Reader(&bytes);
    if rd.take::<8>()? != *FORMAT || rd.u64()? != n as u64 {
        return None;
    }
    let (op_sk, v_sk) = (SigningKey::from_bytes(&rd.take()?), SigningKey::from_bytes(&rd.take()?));
    let id = rd.scalar()?;
    let token = StateToken { kid: u32::from_le_bytes(rd.take()?), cm: rd.take()?, sig: Signature::from_bytes(&rd.take()?) };
    let rho = rd.take()?;
    let list = (0..rd.u64()?)
        .map(|_| {
            Some(Record {
                c: Commitment(rd.point()?),
                d: Commitment(rd.point()?),
                v: rd.u64()?,
                t: u32::from_le_bytes(rd.take()?),
                r: rd.scalar()?,
                s: rd.scalar()?,
            })
        })
        .collect::<Option<Vec<Record>>>()?;
    let mut ns = NullifierSet::default();
    for _ in 0..rd.u64()? {
        let kind: [u8; 1] = rd.take()?;
        let b = rd.take()?;
        ns.insert_if_absent(if kind[0] == 0 { Entry::Nullifier(b) } else { Entry::Tag(b) });
    }
    let (_, verifier, mut paypay) = parties(&op_sk, &v_sk);
    paypay.import_account(ANDI, SavedAccount { id, list, token, rho });
    Some((paypay, verifier, ns))
}

fn history(n: usize, fresh: bool) -> (PayPay, Verifier, NullifierSet) {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target").join(format!("compare-history-{n}.bin"));
    if !fresh {
        if let Some(state) = load(&path, n) {
            println!("Loaded Andi's history of {} records from {}", n - 1, path.display());
            return state;
        }
    }
    let (op_sk, v_sk) = (SigningKey::generate(&mut OsRng), SigningKey::generate(&mut OsRng));
    let (paypay, verifier, ns) = build(n, &op_sk, &v_sk);
    save(&path, n, &op_sk, &v_sk, &paypay, &ns);
    println!("Saved it to {}", path.display());
    (paypay, verifier, ns)
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(f64::total_cmp);
    let mid = v.len() / 2;
    if v.len() % 2 == 1 { v[mid] } else { (v[mid - 1] + v[mid]) / 2.0 }
}

fn ms(secs: f64) -> String {
    format!("{:.1} ms", secs * 1e3)
}

fn kb(bytes: usize) -> String {
    format!("{:.1} KB", bytes as f64 / 1024.0)
}

struct Measured {
    paypay: Vec<f64>,
    verifier: Vec<f64>,
    phi: usize,
    proofs: usize,
}

fn main() {
    let fresh = std::env::args().any(|a| a == "--fresh");
    let mut args = std::env::args().skip(1).filter(|a| a != "--fresh");
    let n: usize = args.next().map(|a| a.parse().expect("N")).unwrap_or(1_000);
    let runs: usize = args.next().map(|a| a.parse().expect("runs")).unwrap_or(10);
    let grid = Grid::for_len(n);
    let (paypay, verifier, ns) = history(n, fresh);

    let mut measured: Vec<Measured> =
        Level::ALL.iter().map(|_| Measured { paypay: Vec::new(), verifier: Vec::new(), phi: 0, proofs: 0 }).collect();
    for run in 1..=runs {
        print!("\rRun {run}/{runs}");
        std::io::Write::flush(&mut std::io::stdout()).ok();
        for (level, m) in Level::ALL.iter().zip(&mut measured) {
            let (mut p, mut v, mut set) = (paypay.clone().with_level(*level), verifier.clone().with_level(*level), ns.clone());
            let req = v.ask(p.issue_tid(ANDI), 100, DAY);
            let t = Instant::now();
            let pkg = p.respond(&req, DAY).unwrap();
            m.paypay.push(t.elapsed().as_secs_f64());
            let t = Instant::now();
            assert!(v.decide(&mut set, &req.x.round_id, &pkg).is_ok(), "{level:?} rejected");
            m.verifier.push(t.elapsed().as_secs_f64());
            (m.phi, m.proofs) = (pkg.size_bytes(), pkg.proofs.size_bytes());
        }
    }

    println!("\n\nOne round at N = {n} (grid {} x {}), {runs} runs per level, median (best)\n", grid.m, grid.n);
    println!(
        "| {:<8} | {:<34} | {:<20} | {:<11} | {:<20} | {:<8} | {:<7} |",
        "Level", "Adds", "PayPay", "vs Baseline", "Verifier", "Phi", "Proofs"
    );
    println!("|{}|{}|{}|{}|{}|{}|{}|", "-".repeat(10), "-".repeat(36), "-".repeat(22), "-".repeat(13), "-".repeat(22), "-".repeat(10), "-".repeat(9));
    let base = median(measured[0].paypay.clone());
    for (level, m) in Level::ALL.iter().zip(&measured) {
        let best = |v: &[f64]| v.iter().copied().fold(f64::MAX, f64::min);
        let paypay = median(m.paypay.clone());
        let change = if *level == Level::Baseline { "".to_string() } else { format!("{:+.0}%", (paypay / base - 1.0) * 100.0) };
        println!(
            "| {:<8} | {:<34} | {:<20} | {:<11} | {:<20} | {:<8} | {:<7} |",
            format!("{level:?}"),
            level.describe(),
            format!("{} ({})", ms(paypay), ms(best(&m.paypay))),
            change,
            format!("{} ({})", ms(median(m.verifier.clone())), ms(best(&m.verifier))),
            kb(m.phi),
            kb(m.proofs),
        );
    }
}
