// Which version of the round runs (decision 35). Each level adds one optimisation
// to the level before it; Baseline is the round before any of them. Every level stays
// in the code, so examples/compare.rs can time them side by side in one run. From B1
// on a level changes the protocol, and then prover and verifier must use the same one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    Baseline, // before decision 35
    A1,       // Karatsuba for S6's diagonals
    A2,       // a precomputed table for g_ran in the re-randomisation
    A3,       // PayPay keeps its list compressed between rounds
    B1,       // protocol: Pi.MIDEq over tid, ONE old record and the domestic ones
    B2,       // protocol: S6 once, on W = C + lambda*D (shuffle/argument.rs)
}

impl Level {
    pub const ALL: [Level; 6] = [Level::Baseline, Level::A1, Level::A2, Level::A3, Level::B1, Level::B2];
    pub const LATEST: Level = Level::B2;

    pub fn describe(self) -> &'static str {
        match self {
            Level::Baseline => "before decision 35",
            Level::A1 => "+ Karatsuba for S6's diagonals",
            Level::A2 => "+ g_ran table for re-randomising",
            Level::A3 => "+ old list kept compressed",
            Level::B1 => "+ Pi.MIDEq over one old record",
            Level::B2 => "+ one S6 for C + lambda*D",
        }
    }
}

// The old records that go into Pi.MIDEq (G5 step 12, G6 step 9). Before B1: all of
// them. From B1 on: the first one only, as the list's representative. That is enough
// because a list under a state token never mixes owners: the round that signed it
// checked Pi.MIDEq over its inputs and Pi.TxVer for its new payment, and the shuffle
// moves the id component of no commitment (it only adds multiples of g_ran). So
// once tid matches one record, it matches all of them. The token's signer is trusted
// for this as it already is for the list itself (honest-but-curious, decision 3).
pub fn mideq_old<T>(level: Level, old: &[T]) -> &[T] {
    if level >= Level::B1 { &old[..old.len().min(1)] } else { old }
}
