use bulletproofs::RangeProof;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use ibc::commitment::Commitment;
use ibc::fulleq::FullEqProof;
use ibc::mideq::MIDEqProof;
use ibc::txver::TxVerProof;
use ibc::veq::VEqProof;

use crate::hash::{Fingerprint, compress};
use crate::request::Request;
use crate::shuffle::ShuffleProof;
use crate::state_token::StateToken;
use crate::tag::TagProof;

// The package Phi the prover sends (G5), split in two: the data the round is about,
// and the proofs. stmt is a fingerprint of the data, and every proof's ctx carries
// stmt, so the data must be complete before the first proof is made.

// What the history starts from.
pub enum Start {
    // Every payment after the first: the last state token, the rho that opens its cm,
    // and the list it signed (in the signed order).
    Token { token: StateToken, rho: [u8; 32], c_old: Vec<Commitment>, d_old: Vec<Commitment> },
    // The first payment (G8): no list, a registration tag instead.
    First { tag: RistrettoPoint },
}

pub struct RoundData {
    pub start: Start,
    pub cm_next: [u8; 32], // cm' for the token this round will issue
    pub c_dom: Vec<Commitment>,
    pub d_dom: Vec<Commitment>,
    pub v_dom: Vec<Commitment>, // two-basis copies of the domestic amounts
    pub c_tx: Commitment,
    pub d_tx: Commitment,
    pub c_out: Vec<Commitment>, // shuffled: front first, then the e expired
    pub d_out: Vec<Commitment>,
    pub e: u32,
    pub v_s: Commitment, // two-basis commitment to the front total S
}

pub struct Proofs {
    pub tag: Option<TagProof>,        // first payment only
    pub mideq: Option<MIDEqProof>,    // when there is an old list or domestic records
    pub txver: TxVerProof,            // c_tx: tid's owner, amount v
    pub fulleq: FullEqProof,          // d_tx: date t_now
    pub domestic: Vec<VEqProof>,      // one bridge per domestic record
    pub sum: VEqProof,                // front total to V_S
    pub shuffle: Option<ShuffleProof>, // when N >= 2
    pub expiry: Option<RangeProof>,   // when e > 0
    pub amounts: RangeProof,
}

pub struct Package {
    pub data: RoundData,
    pub proofs: Proofs,
}

impl Package {
    // Bytes on the wire: 32 per point and per scalar (alur_gabungan.md section 6).
    pub fn size_bytes(&self) -> usize {
        self.data.size_bytes() + self.proofs.size_bytes()
    }
}

impl RoundData {
    pub fn size_bytes(&self) -> usize {
        let start = match &self.start {
            Start::Token { c_old, d_old, .. } => 100 + 32 + 32 * (c_old.len() + d_old.len()),
            Start::First { .. } => 32,
        };
        start + 32 // cm'
            + 32 * (self.c_dom.len() + self.d_dom.len() + self.v_dom.len())
            + 64 // c_tx, d_tx
            + 32 * (self.c_out.len() + self.d_out.len())
            + 4 // e
            + 32 // V_S
    }
}

impl Proofs {
    pub fn size_bytes(&self) -> usize {
        self.tag.as_ref().map_or(0, |_| 128)
            + self.mideq.as_ref().map_or(0, |p| 32 * (1 + p.0.z.len()))
            + 192 // Pi.TxVer
            + 32 * (1 + self.fulleq.0.z.len())
            + self.domestic.iter().map(|p| 32 * (1 + p.0.z.len())).sum::<usize>()
            + 32 * (1 + self.sum.0.z.len())
            + self.shuffle.as_ref().map_or(0, |p| p.size_bytes())
            + self.expiry.as_ref().map_or(0, |p| p.to_bytes().len())
            + self.amounts.to_bytes().len()
    }
}

impl RoundData {
    pub fn c_old(&self) -> &[Commitment] {
        match &self.start {
            Start::Token { c_old, .. } => c_old,
            Start::First { .. } => &[],
        }
    }

    pub fn d_old(&self) -> &[Commitment] {
        match &self.start {
            Start::Token { d_old, .. } => d_old,
            Start::First { .. } => &[],
        }
    }

    // N = old + domestic + this payment.
    pub fn n(&self) -> usize {
        self.c_old().len() + self.c_dom.len() + 1
    }

    // The shuffle's inputs: old list, then domestic records, then this payment (G5 step 4).
    pub fn inputs(&self) -> (Vec<Commitment>, Vec<Commitment>) {
        let c = self.c_old().iter().chain(&self.c_dom).chain([&self.c_tx]).copied().collect();
        let d = self.d_old().iter().chain(&self.d_dom).chain([&self.d_tx]).copied().collect();
        (c, d)
    }

    // The front: the first N - e outputs, summed and kept as the new list.
    pub fn front(&self) -> (&[Commitment], &[Commitment]) {
        let f = self.c_out.len() - self.e as usize;
        (&self.c_out[..f], &self.d_out[..f])
    }

    pub fn tail_dates(&self) -> &[Commitment] {
        &self.d_out[self.d_out.len() - self.e as usize..]
    }

    pub fn encode(&self) -> Encoded {
        Encoded {
            c_old: compress(self.c_old()),
            d_old: compress(self.d_old()),
            c_dom: compress(&self.c_dom),
            d_dom: compress(&self.d_dom),
            c_tx: self.c_tx.0.compress(),
            d_tx: self.d_tx.0.compress(),
            c_out: compress(&self.c_out),
            d_out: compress(&self.d_out),
        }
    }
}

// The round's lists with every point compressed once (decision 34). stmt, the state
// tokens and the shuffle transcript all hash these bytes, so neither side compresses
// a point twice. On the verifier's side this stands in for reading Phi off the wire,
// where each point arrives compressed and is decompressed once.
pub struct Encoded {
    pub c_old: Vec<CompressedRistretto>,
    pub d_old: Vec<CompressedRistretto>,
    pub c_dom: Vec<CompressedRistretto>,
    pub d_dom: Vec<CompressedRistretto>,
    pub c_tx: CompressedRistretto,
    pub d_tx: CompressedRistretto,
    pub c_out: Vec<CompressedRistretto>,
    pub d_out: Vec<CompressedRistretto>,
}

impl Encoded {
    // RoundData::inputs, compressed.
    pub fn inputs(&self) -> (Vec<CompressedRistretto>, Vec<CompressedRistretto>) {
        let c = self.c_old.iter().chain(&self.c_dom).chain([&self.c_tx]).copied().collect();
        let d = self.d_old.iter().chain(&self.d_dom).chain([&self.d_tx]).copied().collect();
        (c, d)
    }

    // RoundData::front, compressed: the list the next state token signs.
    pub fn front(&self, e: u32) -> (&[CompressedRistretto], &[CompressedRistretto]) {
        let f = self.c_out.len() - e as usize;
        (&self.c_out[..f], &self.d_out[..f])
    }
}

// stmt = H("stmt", enc(x), start, cm', C_dom, D_dom, V_dom, c_tx, d_tx, C_out, D_out, e, V_S)
// (G5 step 11). Both sides compute it; a single differing byte fails every proof.
// enc is d.encode(), made once per round.
pub fn statement(x: &Request, d: &RoundData, enc: &Encoded) -> [u8; 32] {
    let h = Fingerprint::new(b"stmt").bytes(&x.to_bytes());
    let h = match &d.start {
        Start::Token { token, rho, .. } => h
            .u32(0)
            .bytes(&token.to_bytes())
            .fixed(rho)
            .compressed(&enc.c_old)
            .compressed(&enc.d_old),
        Start::First { tag } => h.u32(1).point(tag),
    };
    h.fixed(&d.cm_next)
        .compressed(&enc.c_dom)
        .compressed(&enc.d_dom)
        .commitments(&d.v_dom)
        .fixed(enc.c_tx.as_bytes())
        .fixed(enc.d_tx.as_bytes())
        .compressed(&enc.c_out)
        .compressed(&enc.d_out)
        .u32(d.e)
        .point(&d.v_s.0)
        .finish()
}
