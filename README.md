# IBC: Identity-Binding Commitments for Private Cross-Border Payments

A Rust implementation of the **Identity-Binding Commitment (IBC)** scheme and a
set of zero-knowledge proofs built on it. IBC is the identity layer of a
privacy-preserving compliance check for cross-border payments. It lets a payment
provider prove facts about a user's transactions, such as "these payments were
made by the same person" or "this payment is for 3,200", without revealing who the
user is or what else they have paid for.

> **Research prototype.** It exists to show that the protocols are correct and to
> measure what they cost. It has not been audited and should not be used to move
> real money.

---

## The problem

A Japanese tourist in Singapore pays a merchant using their home wallet. Three
parties take part:

| Party | In the example | What it does |
|---|---|---|
| **User** | the tourist | Owns the wallet and the identity behind it |
| **Client** | Alipay+, the network the merchant accepts | Receives the payment request, decides to approve or reject |
| **Server** | PayPay, the tourist's wallet provider | Stores the user's transaction history |

Before the payment goes through, anti-money-laundering rules require a check
along the lines of: *the user's total spending over the last 12 months, including
this payment, must stay below a public limit τ.* Only the server holds the
history needed to answer that, and each side needs something from the other:

- **The user's privacy.** The client should not learn who the user is or what
  they bought before. It needs a yes or no, nothing more.
- **The client's assurance.** The client cannot just take the server's word for
  it. A careless or dishonest server could look up the wrong user, leave out
  transactions, or report a wrong total.

So the server has to run the check **and prove it ran it correctly**, while the
client learns nothing beyond the result. The project calls this *verifiable
two-way private information retrieval*: the server retrieves and aggregates a
user's records for the client, the client cannot see whose records they are, and
the server cannot cheat on the retrieval.

## Where this repository fits

The full system runs in six steps:

1. **Setup and commit.** The wallet provider gives the user a transaction ID
   `tid` that is itself an IBC commitment to the user's ID. It looks like 32
   random bytes; without the secret opening, nobody can tell whose it is.
2. **Payment request.** The client receives `x = (tid, v, T, f)`: the transaction
   ID, the amount `v`, the look-back period `T` (one year), and the rule `f`
   (total within the period ≤ τ).
3. **Retrieval.** The server maps `tid` to the user and gathers their records
   from the last `T`.
4. **Identity and value proofs.** The server proves that the records it is
   adding up belong to the same user as `tid`, and that the new transaction is
   for the declared amount `v`.
5. **Compliance proofs.** The server shuffles the records, keeps only those
   inside the one-year window, updates the history without revealing which entry
   changed, and proves that `f` holds.
6. **Decision.** The client checks every proof and approves or rejects.

**This repository implements steps 1 and 4**: the commitment scheme and the proofs
over it. Step 5 (verifiable shuffle, sliding window, oblivious update, verified
expiry) is a separate work package that builds on these commitments. None of the
code here depends on it.

Real settlement between banks, currency exchange, AML risk scoring, and wallet
security are outside the scope of both.

## The commitment

A commitment works like a sealed envelope. You publish it now; nobody can see
inside, and you cannot later claim it held something else. A standard Pedersen
commitment seals one number. IBC adds a third generator so that one commitment
seals two things: **who** is paying and **how much**.

```
c = id·g_iden + v·g_val + r·g_ran
```

| Symbol | Meaning |
|---|---|
| `id` | the user's identity, hashed to a number |
| `v` | the transaction amount |
| `r` | a fresh random number, new for every commitment (the "blinding") |
| `g_iden, g_val, g_ran` | three fixed public points on the elliptic curve |

The written specification uses multiplicative notation,
`c = g_iden^id · g_val^v · g_ran^r`. It is the same equation; elliptic-curve
libraries write the group operation as addition.

- **Hiding.** Because `r` is fresh and random, two commitments by the same user
  for the same amount look completely unrelated. This holds even against an
  attacker with unlimited computing power.
- **Binding.** Nobody can open `c` to a different `(id, v)`, as long as nobody
  knows a mathematical relation between the three generators. Finding one is
  as hard as the discrete-logarithm problem.
- **Size.** Every commitment is a single point of the ristretto255 group, 32
  bytes.

**Where the generators come from.** Each generator is produced by hashing a fixed
public label (`IBC/v1/gen/iden`, `IBC/v1/gen/val`, `IBC/v1/gen/ran`) onto the
curve. Nobody chooses them, so nobody holds a trapdoor, and anyone can recompute
them to confirm they are using the same parameters. This matters. If the wallet
provider picked the generators itself, it could pick them with a hidden relation
between them and then "prove" that two different users are the same person.

## The proofs

Each proof lets the party holding the secret openings (in the payment setting,
the server) convince a verifier of one statement about some commitments,
revealing nothing else. The identity, the amount, and the random blinding all
stay hidden unless the statement itself makes them public.

### Basic method

These two proofs are the ones the original design calls for.

| Proof | Statement | Use in the payment flow | Size |
|---|---|---|---|
| **Π.IDEq** | `c0` and `c1` hold the same identity | Link a new payment to the user's earlier records without learning who the user is | 96 B |
| **Π.VVer** | `c` holds the public amount `v'` | Show that the committed transaction is for the amount in the payment request | 96 B |

### Advanced method

These build on the same commitment and parameters, so everything proved for the
Basic method still holds.

| Proof | Statement | Use | Size |
|---|---|---|---|
| **Π.MIDEq** | `c1, …, cn` all hold the same identity | One proof for a whole transaction history instead of `n − 1` pairwise proofs | 96 B for any `n` |
| **Π.VEq** | `c0` and `c1` hold the same amount, which stays hidden | The sender's and receiver's records of one transfer agree | 96 B |
| **Π.FullEq** | `c0` and `c1` hold the same identity *and* amount | Show a commitment was re-randomised without its contents changing | 64 B |
| **Π.TxVer** | `c_tx` has the same identity as the user's registration commitment `c_ref`, *and* holds `v'` | The whole per-payment check, as one proof that cannot be split in two | 192 B |
| **BatchVer** | Checks many Π.IDEq proofs in one go | An auditor or regulator verifying a large number of transactions | none (a faster way to verify) |

Every proof is bound to a **context string** `ctx`, usually the transaction ID. A
proof made for one transaction fails for any other, so it cannot be copied onto a
different transaction.

## How the proofs work

All of the proofs rest on one idea. Take Π.IDEq. Subtracting two commitments
gives:

```
c0 − c1 = (id0 − id1)·g_iden + (v0 − v1)·g_val + (r0 − r1)·g_ran
```

If the identities are equal, the `g_iden` term drops out and what remains is
built from `g_val` and `g_ran` alone. The prover shows it knows how to write
`c0 − c1` that way. If the identities were different, being able to do so would
expose a relation between the generators, which is assumed to be infeasible.
Note that the prover never needs the identity itself, only the amounts and
blinding factors.

Every other proof uses the same trick: build a public point `U` in which the part
being claimed cancels out, then prove knowledge of how to write `U` using the
generators that remain.

| Proof | `U` | Remaining generators | Cancels when |
|---|---|---|---|
| Π.IDEq | `c0 − c1` | `g_val, g_ran` | identities are equal |
| Π.VVer | `c − v'·g_val` | `g_iden, g_ran` | the amount is `v'` |
| Π.VEq | `c0 − c1` | `g_iden, g_ran` | amounts are equal |
| Π.FullEq | `c0 − c1` | `g_ran` | identities and amounts are equal |
| Π.MIDEq | a random combination of every `c1 − ci` | `g_val, g_ran` | all identities are equal |
| Π.TxVer | both Π.IDEq's and Π.VVer's, under one challenge | both pairs | both claims hold |

The proof itself is a three-message **Sigma protocol**. The prover sends a
random-looking commitment `t`, receives a random challenge `β`, and answers with
responses `z` that only someone who knows the secrets could compute. To make it a
single message, the challenge is computed with the **Fiat–Shamir** transform:

```
β = Hash(protocol name, generators, statement, ctx, t)
```

A proof then becomes a fixed object that can be stored with the transaction and
checked later by anyone authorised to, for example an auditor weeks after the
payment. Hashing the full statement, and not only `t`, is what stops an attacker
from forging a proof for commitments it never opened.

In the code this is written once, as a generic engine in
[src/sigma.rs](src/sigma.rs). Each protocol file is a short wrapper that supplies
its `U`, its generators, its secret witness and its own domain label. Π.TxVer is
written out by hand because it runs two equations under a single challenge.
BatchVer is a verifier rather than a proof: it combines many verification
equations with random weights and checks them all in a single multi-scalar
multiplication.

## Assumptions and known limits

- **Security assumptions.** Security rests on the discrete-logarithm assumption
  in ristretto255 and on modelling the hash as a random oracle. A cheating prover
  gets a false statement accepted with probability at most about `(Q+1)/p`, where
  `p ≈ 2^252` is the group order and `Q` is the number of hashes it tries. For
  BatchVer the bound is `2^-128` per batch.
- **No range proof.** Amounts are numbers modulo `p`, so a committed amount could
  be `p − 1`, which behaves like −1. Π.VVer is not affected, because it pins the
  amount to a public number. Π.VEq only proves that two hidden amounts are equal,
  not that either is sensible. This prototype assumes amounts are well-formed
  when issued; a range proof is future work.
- **Reference commitments must be authenticated.** Π.TxVer proves that a
  transaction matches the user's registration commitment `c_ref`. If the prover
  could make `c_ref` up, the proof would say nothing about a real user. `c_ref`
  must be signed by whoever registered the user (at KYC time) or kept in an
  authenticated registry, and the verifier must check that first. This happens
  outside the proof and is not implemented here.
- **Equality proofs reveal linkage.** Π.IDEq and Π.MIDEq never reveal *who* the
  user is, but they do reveal that some commitments belong to the *same* person.
  They should only be given to an authorised verifier. Proofs that only the
  intended verifier can check are future work.

## Project layout

```
src/
  params.rs       Setup: the three generators, hashed from public labels
  commitment.rs   Commit and Verify
  transcript.rs   Fiat–Shamir challenges (Merlin transcript)
  sigma.rs        the shared proof engine
  schnorr.rs      single-generator warm-up proof
  ideq.rs         Π.IDEq
  vver.rs         Π.VVer
  veq.rs          Π.VEq
  fulleq.rs       Π.FullEq
  txver.rs        Π.TxVer
  mideq.rs        Π.MIDEq
  batchver.rs     BatchVer
benches/          speed measurements (per protocol, and how they scale)
tests/            proof sizes; false approval and rejection counts
scripts/          report.py, which turns a benchmark run into results/
results/          tables and charts from the latest run
pseudocode/       every protocol written as pseudocode (PDF)
```

## Running it

Requires Rust 1.85 or newer (edition 2024).

```bash
cargo test                   # run the tests
cargo bench                  # measure speed (about 8-10 minutes)
python scripts/report.py     # build results/ from the measurements (needs matplotlib)
```

`report.py` also runs the size test and the false approval / rejection test,
which runs every proof 10,000 times per scenario.

## Results

Measured on an AMD Ryzen 7 6800H laptop, on one core, on 2026-09-27. The targets
come from the project's requirements. Full tables and charts are in
[results/README.md](results/README.md).

| Metric | Target | Measured |
|---|---|---|
| Time to create a commitment | under 10 ms | 0.083 ms |
| Time to create a proof (slowest) | under 10 ms | 0.175 ms |
| Time to check a proof (slowest) | under 5 ms | 0.198 ms |
| Transactions checked per second | over 100 | 8,511 |
| Commitment size | 32-64 B | 32 B |
| False approvals | 0 | 0 out of 190,000 |
| False rejections | 0 | 0 out of 70,000 |

Every target is met. Checking one Π.MIDEq proof over 1,000 commitments is 5.2
times faster than checking 999 separate Π.IDEq proofs, and the proof stays at 96
bytes instead of growing to 95.9 KB. BatchVer checks 10,000 proofs at 47 µs each,
against 68 µs each when checked one at a time.

## Built on

- **Pedersen commitments** (Pedersen, CRYPTO 1991), extended here with a third
  generator.
- **Okamoto's representation proof** (Okamoto, CRYPTO 1992), the Sigma protocol
  behind every proof in this crate.
- **The Fiat–Shamir transform** (Fiat and Shamir, CRYPTO 1986), in the strong form
  that hashes the full statement (Bernhard, Pereira and Warinschi, ASIACRYPT 2012).
- [curve25519-dalek](https://github.com/dalek-cryptography/curve25519-dalek) for
  the ristretto255 group, and [merlin](https://github.com/dalek-cryptography/merlin)
  for transcripts.
