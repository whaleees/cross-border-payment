use ibc::ctx::RoundCtx;

// Stages of one round (alur_gabungan.md, section 4; decision 24).
pub const STAGE_TAG: u8 = 0; // Pi.Tag, first payment only
pub const STAGE_MIDEQ: u8 = 1; // Pi.MIDEq over (tid, old list, domestic)
pub const STAGE_NEW_PAIR: u8 = 2; // Pi.TxVer for c_tx, Pi.FullEq for d_tx
pub const STAGE_DOMESTIC: u8 = 3; // Pi.VEq bridge per domestic record, slot = record
pub const STAGE_SHUFFLE: u8 = 4;
pub const STAGE_EXPIRY: u8 = 5; // Bulletproofs over the tail dates
pub const STAGE_TOTAL: u8 = 6; // Pi.VEq for the sum (slot 0), Bulletproofs for amounts (slot 1)

// Which list a proof is about. Kresna's RoundCtx names 0 value and 1 age; here
// the dates replace ages, and 2 marks a proof over both lists.
pub const VALUE: u8 = 0;
pub const DATE: u8 = 1;
pub const BOTH: u8 = 2;

// One round's binding: round_id comes from the verifier, stmt is the fingerprint of
// everything the round is about. Every proof's ctx carries both, so a proof cannot
// move to another round, another stage, or other data.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Round {
    pub round_id: [u8; 32],
    pub stmt: [u8; 32],
}

impl Round {
    pub fn ctx(&self, stage: u8, vector: u8, slot: u32) -> [u8; RoundCtx::LEN] {
        RoundCtx { round_id: self.round_id, stage, vector, slot, prev: self.stmt }.to_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    fn round() -> Round {
        Round { round_id: [0xA; 32], stmt: [0x5; 32] }
    }

    #[test]
    fn ctx_is_kresnas_78_byte_layout() {
        let c = round().ctx(STAGE_SHUFFLE, BOTH, 0);
        let direct = RoundCtx { round_id: [0xA; 32], stage: 4, vector: 2, slot: 0, prev: [0x5; 32] };
        assert_eq!(c.len(), 78);
        assert_eq!(c, direct.to_bytes());
    }

    #[test]
    fn every_proof_in_a_round_gets_its_own_ctx() {
        // The table of section 4, with three domestic records. No two proofs in one
        // round may share a ctx, or one could be swapped for the other.
        let r = round();
        let mut used = vec![
            r.ctx(STAGE_TAG, VALUE, 0),
            r.ctx(STAGE_MIDEQ, VALUE, 0),
            r.ctx(STAGE_NEW_PAIR, VALUE, 0),
            r.ctx(STAGE_NEW_PAIR, DATE, 0),
            r.ctx(STAGE_SHUFFLE, BOTH, 0),
            r.ctx(STAGE_EXPIRY, DATE, 0),
            r.ctx(STAGE_TOTAL, VALUE, 0),
            r.ctx(STAGE_TOTAL, VALUE, 1),
        ];
        used.extend((1..=3).map(|j| r.ctx(STAGE_DOMESTIC, VALUE, j)));

        let distinct: HashSet<_> = used.iter().collect();
        assert_eq!(distinct.len(), used.len());
    }

    #[test]
    fn round_id_and_stmt_both_change_the_ctx() {
        let r = round();
        let other_round = Round { round_id: [0xB; 32], ..r };
        let other_stmt = Round { stmt: [0x6; 32], ..r };
        assert_ne!(r.ctx(STAGE_MIDEQ, VALUE, 0), other_round.ctx(STAGE_MIDEQ, VALUE, 0));
        assert_ne!(r.ctx(STAGE_MIDEQ, VALUE, 0), other_stmt.ctx(STAGE_MIDEQ, VALUE, 0));
    }
}
