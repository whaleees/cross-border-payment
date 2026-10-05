const TAG: &[u8; 8] = b"IBCctx/1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RoundCtx {
    pub round_id: [u8; 32], // issued by the verifier, fresh for every round
    pub stage: u8,          // the stage of the round that consumes the proof
    pub vector: u8,         // which commitment vector: 0 = value, 1 = age
    pub slot: u32,          // output index; 0 when the proof covers a whole vector
    pub prev: [u8; 32],     // hash of the round's earlier messages; zeros if unused
}

impl RoundCtx {
    pub const LEN: usize = 8 + 32 + 1 + 1 + 4 + 32;

    pub fn to_bytes(&self) -> [u8; Self::LEN] {
        let mut out = [0u8; Self::LEN];
        out[0..8].copy_from_slice(TAG);
        out[8..40].copy_from_slice(&self.round_id);
        out[40] = self.stage;
        out[41] = self.vector;
        out[42..46].copy_from_slice(&self.slot.to_le_bytes());
        out[46..78].copy_from_slice(&self.prev);
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> RoundCtx {
        RoundCtx { round_id: [7; 32], stage: 2, vector: 1, slot: 5, prev: [9; 32] }
    }

    #[test]
    fn layout_is_fixed() {
        let b = sample().to_bytes();
        assert_eq!(b.len(), 78);
        assert_eq!(&b[0..8], b"IBCctx/1");
        assert_eq!(b[8..40], [7; 32]);
        assert_eq!(b[40], 2);
        assert_eq!(b[41], 1);
        assert_eq!(b[42..46], 5u32.to_le_bytes());
        assert_eq!(b[46..78], [9; 32]);
    }

    #[test]
    fn every_field_changes_the_bytes() {
        let base = sample();
        for other in [
            RoundCtx { round_id: [8; 32], ..base },
            RoundCtx { stage: 3, ..base },
            RoundCtx { vector: 0, ..base },
            RoundCtx { slot: 6, ..base },
            RoundCtx { prev: [0; 32], ..base },
        ] {
            assert_ne!(other.to_bytes(), base.to_bytes());
        }
    }
}
