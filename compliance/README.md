# Compliance: verifiable shuffle and sliding-window limit check over IBC

A Rust implementation of step 5 of the cross-border payment flow described in the
[repository README](../README.md), together with the round that runs it. It builds
on the `ibc` crate (the identity-binding commitments and proofs in [../src](../src))
without changing it.

> **Research prototype.** It exists to show that the protocol is correct and to
> measure what it costs. It has not been audited and should not be used to move
> real money.

The protocol is specified as pseudocode: one round as protocols G0–G10, the shuffle
as S1–S6. Function comments name the step they implement, for example `G6 step 15`.

---

## What one round checks

A user pays abroad. The verifier of that country (say Alipay+ in Singapore) asks
the wallet provider (PayPay) whether the user's spending over the last `T` days,
this payment included, stays under the verifier's limit `B`. PayPay answers with
one package; the verifier checks it and approves or rejects. The verifier never
sees who the user is, what the earlier payments were, or the total.

Every transaction is a pair of commitments: `c = id·g_iden + v·g_val + r·g_ran`
(owner and amount, Kresna's IBC) and `d = t·g_val + s·g_ran` (the day, no identity).

| The verifier is convinced that | By |
|---|---|
| The history is the latest one a verifier approved, nothing left out or rolled back | A state token (Ed25519 over the list) and a nullifier recorded once in a shared set |
| A first payment is not a second start for someone already registered | A registration tag `id·g_tag` and a two-clause proof (Π.Tag) |
| Every old and domestic record belongs to the payer | Π.MIDEq over `tid` and the records |
| This payment is for `v`, by the payer, dated today | Π.TxVer for `c_tx`, Π.FullEq for `d_tx` |
| No domestic amount is negative | Π.VEq to a two-basis copy, then Bulletproofs (64 bit) |
| The output list is the input list shuffled, with amounts and days still paired | A Bayer–Groth shuffle argument over an `m × n` grid |
| Everything dropped had expired | Bulletproofs (16 bit) on `θ − 1 − t` for every record in the tail |
| The kept total `S` is at most `B` | Π.VEq from the summed front to `V_S`, then Bulletproofs on `S` and `B − S` |

The shuffle is what hides which records expired and where this payment sits in the
new list: the verifier only learns how many records were dropped.

---

## Project layout

```
src/
  params.rs        g_tag, the shuffle's commitment key, T, theta (window_start)
  hash.rs          H(label, ...) = SHA-256("compliance/v1/" || label || 0x00 || ...)
  ctx.rs           stage numbers and Kresna's RoundCtx with prev = stmt
  tag.rs           Π.Tag, the registration tag proof
  state_token.rs   state token, nullifier commitment, nullifier
  operator.rs      nullifier set and the signed registry of verifiers
  range.rs         Bulletproofs: tail expiry, amounts and S <= B
  shuffle/         S1-S6: argument, product, hadamard, zero, svp, multiexp
  request.rs       the verifier's signed request x
  package.rs       the package Phi and its statement stmt
  paypay.rs        the prover's side of a round
  verifier.rs      the verifier's side of a round
tests/story.rs     Singapore, Japan, Thailand, Singapore, and a year later
benches/           components.rs (one proof at a time), scaling.rs (by N and m)
examples/          breakdown.rs: where one round's time goes, step by step
```

## Running it

From this folder:

```bash
cargo test                                   # unit tests and the story
cargo bench                                  # about 15 minutes
cargo bench --features vartime-prover --bench scaling -- shuffle
                                             # the shuffle with a variable-time prover
cargo run --release --example breakdown -- 1000
                                             # one round at N = 1,000, step by step
```

The prover's multi-scalar multiplications run in constant time by default, because
their scalars encode the secret permutation. The `vartime-prover` feature swaps in
the variable-time versions, only to measure what constant time costs.

---

## Results

Measured on an Intel Core i7-13650HX laptop, on one core, release build, on
2026-10-17; medians from criterion. This is a different machine from the one in
the repository README, so the two sets of numbers should not be compared directly.

**One proof at a time** (`benches/components.rs`):

| Component | Prove | Verify | Size |
|---|---|---|---|
| Π.Tag | 0.12 ms | 0.12 ms | 128 B |
| State token over 10 pairs (sign / check) | 0.10 ms | 0.11 ms | 100 B |
| Bulletproofs, 2 tail dates, 16 bit | 3.9 ms | 0.60 ms | 608 B |
| Bulletproofs, `S` and `B − S`, 64 bit | 14.7 ms | 1.5 ms | 736 B |
| Shuffle, `N` = 100 (10 × 10) | 30.3 ms | 6.1 ms | 4.7 KB |

**The shuffle by `N`**, at the protocol's grid `m = min(16, ⌊√N⌋)`
(`benches/scaling.rs`). The prover's secret multi-scalar multiplications run in
constant time by default; the second column swaps in variable time.

| `N` | Grid | Prove | Prove, variable time | Verify | Proof |
|---|---|---|---|---|---|
| 100 | 10 × 10 | 29.5 ms | 18.6 ms | 6.0 ms | 4.7 KB |
| 1,000 | 16 × 63 | 387 ms | 177 ms | 35 ms | 14.7 KB |
| 10,000 | 16 × 625 | 3.62 s | 1.26 s | 300 ms | 102.5 KB |

**The shuffle by `m`** at `N` = 1,000, the trade-off between prover time and proof
size:

| `m` | Grid | Prove | Prove, variable time | Verify | Proof |
|---|---|---|---|---|---|
| 1 | 1 × 1000 | 96 ms | 43 ms | 43 ms | 94.2 KB |
| 4 | 4 × 250 | 131 ms | 65 ms | 38 ms | 40.5 KB |
| 16 | 16 × 63 | 387 ms | 177 ms | 35 ms | 14.7 KB |
| 32 | 32 × 32 | 663 ms | 303 ms | 38 ms | 14.3 KB |

**A whole round** with `N` pairs: PayPay answering the request (G3–G5) and the
verifier checking and deciding (G6–G7). The package Φ includes the lists of
commitments the verifier needs; the proofs are the smaller part.

| `N` | PayPay | PayPay, variable time | Verifier | Φ | of which proofs |
|---|---|---|---|---|---|
| 10 | 17.2 ms | 16.4 ms | 3.9 ms | 4.4 KB | 3.0 KB |
| 100 | 49.2 ms | 38.1 ms | 9.7 ms | 18.6 KB | 5.9 KB |
| 1,000 | 442 ms | 236 ms | 51 ms | 141.0 KB | 15.8 KB |

What the numbers say:

- Proof sizes match the formulas exactly: `32·(9m + 5n + 11)` bytes for the shuffle
  with `m ≥ 2`, `32·(3n + 13)` with one row.
- Computing each diagonal of the multi-exponentiation argument as one multi-scalar
  multiplication is what makes a 16-row grid affordable. The earlier √N-grid
  implementation, which multiplied point by point, took 48 s to prove at
  `N` = 10,000 on this machine; here it is 3.6 s in constant time and 1.3 s in
  variable time.
- Constant time costs the prover about 2–3 times. The verifier only handles public
  values, so its commitments always run in variable time. At `N` = 1,000 its shuffle
  check takes 35 ms, against 46 ms when it shared the prover's constant-time
  routine.
- Each side compresses every point of a round once and hashes those bytes into
  stmt, the state tokens and the shuffle transcript; before, the same point was
  compressed up to three times. That took the verifier at `N` = 1,000 from 81 ms
  to 51 ms. The one compression left, about 14 ms, stands in for reading Φ off the
  wire. PayPay saves as much, which shows in the variable-time column (255 to
  236 ms) but is lost in the noise of the constant-time one, where the diagonals
  of the multi-exponentiation argument alone take about 290 ms
  (`examples/breakdown.rs`). The tables above time each component on its own,
  compressing its own lists, so they did not change.
- At `N` = 1,000 the lists in Φ are 125 KB and the proofs 16 KB. As long as the
  verifier sees every commitment, which is what makes the shuffle hide anything,
  the message cannot be smaller than linear in `N`.

---

## Assumptions and known limits

- **Domestic payments are trusted.** PayPay reports its own domestic payments.
  Their amounts are proved non-negative, but nothing can force PayPay to report
  them. The limit on cross-border payments holds even if PayPay cheats; the limit
  including domestic payments holds if PayPay reports them honestly.
- **One person, one `id`.** PayPay issues KYC. The registration tag stops a second
  start for the same `id`, not a new `id` for the same person.
- **No collusion** between PayPay and a verifier, between verifiers, or between
  PayPay and the operator. The operator never deletes entries and lists only valid
  verifier keys.
- **What a verifier learns:** the amount and date of the payment it handles; the
  list length `N`, the number of expired records `e` and of new domestic records;
  which verifier signed the previous state token; the outcome.
- **The nullifier set is in memory** here. A deployment needs a database with a
  unique key, so that "record if absent" is atomic.
- **No formal proof yet** for the shuffle adapted from ElGamal ciphertexts to two
  lists of IBC commitments. The tests check every attack the design names.

## Built on

- **Kresna's `ibc` crate**: commitments, Π.MIDEq, Π.TxVer, Π.VEq, Π.FullEq,
  `RoundCtx`, `derive_generators`, the Merlin-based `Challenge`.
- **Bayer and Groth**, "Efficient Zero-Knowledge Argument for Correctness of a
  Shuffle", EUROCRYPT 2012, with the sub-arguments of its full version.
- **Bulletproofs** (Bünz et al., IEEE S&P 2018) through the
  [`bulletproofs`](https://crates.io/crates/bulletproofs/5.0.0) crate 5.0.0.
- **Chaum and Pedersen**, CRYPTO 1992, for the two-clause tag proof.
- **Ed25519** (RFC 8032) through [`ed25519-dalek`](https://crates.io/crates/ed25519-dalek/2.2.0) 2.2.0.
- **Nullifiers** as in Zerocash (ePrint 2014/349).
