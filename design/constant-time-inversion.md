# Constant-time inversion for the Pasta fields: one algorithm, three implementations

The plan for replacing the crate's inversion by the current state of the art, with the AArch64
assembly, the x86-64 assembly, and a portable Rust implementation following one algorithm block
for block, so that the verification above the blocks is done once. The correctness argument
that the Lean development follows is
[constant-time-inversion-proof.md](constant-time-inversion-proof.md). The shared Lean layer
lives under `lean/PastaAsm/Inversion/`.

Produced 2026-09-27 by a Claude Fable 5.1 agent, from a design discussion with @daira, after a
survey of the literature and measurements on an Apple M4 Max (recorded in @daira's working
notes). Companion drafts kept outside the repository: the Lean outline of the theorems to be
proved, and the Python models behind the numerical checks.

## Aim

Replace the Pornin-style inversion of pasta-asm#10 by the state of the art, and have the
AArch64 assembly, the x86-64 assembly, and a portable Rust implementation follow one algorithm,
block for block, so that the verification above the blocks is done once. The algorithm is the
serial variant of Bernstein, Chen, Harrison, Huang, Maxwell, Wang, Wuille, and Yang,
"Accelerating and verifying constant-time modular inversion" (EUROCRYPT 2026), as implemented
and HOL Light–verified in s2n-bignum's `bignum_montinv_p256` (Apache-2.0 OR ISC OR MIT-0).
Measured there, it is 1.4 to 1.9 times faster than the Pornin family on both ISAs. On @daira's
M4 Max MacBook #10 takes 1.69 µs and Zakura's variable-time safegcd 1.12 µs; the target is at
or below the variable-time figure.

## The algorithm (fixed for all three implementations)

Inputs: a canonical Montgomery residue `x < p` (debug-asserted, as for the other entry points),
one of the two Pasta primes as `modulus`, and `inv`. Output: the canonical Montgomery residue
`z` with `x * z ≡ 2^512 (mod p)`, that is the Montgomery form of the inverse; `x = 0` gives
`z = 0`.

State: `f`, `g` signed integers of at most 256 bits in magnitude, kept as four words plus a
sign word; `u`, `v` unsigned values below `2^256`, four words; `d = 2δ`, a small signed
integer, `d₀ = 1` (the half-delta start). Initially `f = p`, `g = x`, `u = 0`,
`v = 2^562 mod p`.

Ten rounds. Each round:

1. `divstep59 (d, f mod 2^64, g mod 2^64) → (d', M)`: the exact transition matrix of 59
   divsteps, computed from the low words alone, as three packed batches of 20, 20, and 19 steps
   in which the coefficients ride in the upper bits of the same two words, then two 2×2 integer
   products.
2. `updateFG (M, f, g) → ((m00 f + m01 g) / 2^59, (m10 f + m11 g) / 2^59)`, exact divisions, in
   five-word signed arithmetic.
3. `updateUV (M, u, v) → (amontred (m00 u + m01 v), amontred (m10 u + m11 v))`, where
   `amontred t` adds `2^61 p`, performs one word of Montgomery reduction, and returns a value
   below `2^256`, congruent to `t / 2^64`. The extra five bits per round, 64 against 59, are
   why the start is `2^562 = 2^(512 + 5·10)`.

The tenth round computes only `u`, folds in the sign of the final `f` (which is `±1`), and
reduces strictly by one conditional subtraction. Invariant after round `i`:
`(f, g) ≡ x · 2^(5i − 562) · (u, v) (mod p)`. After ten rounds `g = 0`, `f = ±1`, and
`x · (±u) ≡ 2^512`.

Block interfaces are the same in all three implementations, and every implementation composes
them the same way in a fixed loop. A change to what a block computes is a change to the shared
model.

## Where things live

- **Lean model and proofs: pasta-asm, `lean/PastaAsm/Inversion/`** (shared), with per-ISA block
  equality theorems in `lean/PastaAsm/{AArch64,X86_64}/Spec/*.lean`. The shared theorem
  `montInv_spec` is about `montInvModel`, the composition of the word-level functions. The
  composition `invert` of the blocks is one Lean definition over a record of a backend's
  blocks, proved equal to the model once from the record of their specifications, so each ISA
  proves its transcribed blocks equal to the word-level functions and instantiates the two
  records.
- **AArch64 and x86-64 blocks: pasta-asm**, register-only `asm!` blocks adapted from
  s2n-bignum's ARM and x86 `bignum_montinv_p256` with the Pasta constants and the Pasta
  `amontred` (the modulus shape `modulus[2] = 0`, `modulus[3] = 2^62` replaces P-256's), under
  the crate's Apache-2.0.
- **Portable Rust: pasta-asm, `src/portable.rs`** (@daira's decision, 2026-09-28, revising the
  placement in pasta_curves of 2026-09-27: the formalization is shared, so the same block
  decomposition and driver serve it). The six blocks are written against the block contracts
  as the Lean specifications state them, in the shape of the word-level model (the packed
  recurrence with masks, the decoder's formula, limb arithmetic modulo `2^320`), and `invert`
  runs them on every target that has no assembly blocks, and under `pasta_asm_disable`. They
  are checked against the same known answers as the assembly blocks; an Aeneas translation to
  Lean is the intended way to make the link a proof, by instantiating `InvertBlocks` with the
  translated functions.
- **Vectors:** one file, inputs chosen to exercise the edge cases (0, 1, p−1, powers of two,
  the 590-step extremal inputs from the paper's method if reproducible, random), expected
  values computed independently; replayed by every backend's tests and by Lean.

## Proof obligations, grouped by where the effort is shared

Shared, ISA-independent ([the proof](constant-time-inversion-proof.md) gives the arguments):

1. Divstep algebra: linearity (a transition matrix per step), locality (n steps depend only on
   `d` and the low n bits), the matrix bound (row sums at most `2^n`, entries in
   `(−2^n, 2^n]`), invariance of `gcd` and of `max(|f|, |g|)`.
2. Packing: the twenty-step packed recurrence on two 64-bit words equals the true matrix, with
   the coefficient parts recoverable from the upper bits under the half-open range.
3. Five-word arithmetic: `updateFG` is exact; `amontred` returns a value `t'` with
   `8 t' < 2^254 + 9p`, hence below `2p` and below `2^256`, congruent to `t / 2^64`, from
   `|t| < 2^315` and `2^254 ≤ p < 2^255`.
4. The round invariant and the final formula, including `x = 0 ↦ 0`.
5. Termination: `g = 0` after 590 half-delta divsteps for `0 ≤ g ≤ f < 2^256`, `f` odd. Proved
   by a hull certificate (the user's decision, 2026-09-27). The certificate is Bernstein's
   "hull light" data of 2023 (`https://cr.yp.to/2023/hull-light-20230416.sage`, public domain),
   whose check and proof in HOL Light are in `jrh13/hol-light` under `Divstep/` (Harrison); the
   paper's Section 4.3 describes the same argument, and its site has no separate supplement.
   Its shape: two explicit 80-point rational hulls `S_{1/2}` and `S_{−1/2}`, every other `S_δ`
   being defined as a linear image of `S_{1/2}` (with a factor `33/32` for `|δ| ≥ 5/2`); the
   shrink factor `λ' = 30902639/41749730`; and three exact checks. (a) Eight inclusions
   `M S_δ ⊆ λ'^k S_δ'` for the step maps `M_{−1} (x, y) = (y, (y − x)/2)`,
   `M_1 (x, y) = (x, (y + x)/2)`, and `M_0 (x, y) = (x, y/2)`, each certified half-plane by
   half-plane with two Farkas multipliers; every other transition is an equality by definition
   or follows from convexity. (b) The initial containment: the triangle `0 ≤ y ≤ x ≤ 1` scaled
   by `2753/4096` lies in `Hull S_{1/2}`, so `0 ≤ g ≤ f ≤ 2^b` gives
   `(f/H, g/H) ∈ Hull S_{1/2}` for `H = 2^b · 4096/2753`. (c) A lattice-point endgame: with
   `L = 3047/2048` the scaled hulls contain no integer point with `y ≠ 0`, checked through an
   outer box and the enumeration of the few candidate points, so that once
   `2^b λ'^n ≤ L · 2753/4096` the state has `g_n = 0`. The simpler endgame (`|x| < 1` or
   `|y| < 1` after `n` steps) fails at `n = 590` and first passes at 591, so it is not used;
   for `b = 256` and `n = 590` the slack is about 5 %. In Lean, done: the half-planes and the
   Farkas records are generated data (`HullData.lean`, from
   `lean/scripts/hull_certificate.json` by `gen_hull.py`); the inclusion checks are evaluated
   by the kernel (`HullCert.lean`); and the argument over abstract regions, following
   Harrison's structure, ends in `terminationBound_of_certified` (`HullBound.lean`), with the
   range of `δ` handled by the definitional formula and lemmas rather than a finite table.
   `verify_hull_certificate.py` re-checks the JSON independently in exact arithmetic (724
   Farkas records, 16 lattice points, under a second), in CI. The triangle covers only `g ≤ f`.
   For the square, which would admit a non-canonical `x` up to `2^256`, the largest admissible
   scale is `5193/8192`. With that scale 590 steps fail by 0.19 % and 591 pass, so the input
   stays canonical.

Per ISA:

6. Each `asm!` block's generated transcription equals the corresponding word-level function.
   The generator needs the instructions the blocks use: AArch64 `ccmp`, `cneg`, `tst`, `sbfx`,
   `mneg`, `msub`, `csetm`; x86-64 `cmov` forms, `test`, `imul` (signed), `sar`, `neg`.

Shared, over any ISA's blocks:

7. The driver's composition equals `montInvModel`. The driver is one Rust function over a
   backend's blocks, mirrored once in `Compositions.lean` over a record of the blocks and
   proved equal to the model from the record of the block specifications
   (`Inversion/Composition.lean`); an ISA instantiates the two records.

Portable Rust:

8. Vectors, and the same block decomposition; Aeneas if it takes the code.

## Milestones

- **M0** this plan, the proof document, and a Lean outline of the theorems elaborating with
  `sorry`.
- **M1** word-level Python model (packed batches, unpacking, 5-word updates, `amontred`)
  checked against the integer model; the vectors file generated from it and from an independent
  `pow`.
- **M2** Lean shared layer: definitions of the word-level functions, obligations 1–4 proved, 5
  as a hypothesis; `#eval` of `montInvModel` agrees with the Python model on the vectors.
- **M3** portable Rust against the block contracts, in pasta-asm, provided on every target;
  the known answers and the inversion checks over it; benchmark.
- **M4** AArch64 blocks; generator extensions; obligation 6 for AArch64; `invert_entry_spec`.
- **M5** x86-64 blocks; the same. The AArch64 block proofs separate the instruction plumbing (flags,
  the conditional instructions, the generated skeletons) from word lemmas that do not depend on the
  ISA: the two's-complement row identities, the shift by 59, the three cases of a packed step, the
  decoder arithmetic, and the batch iteration. Those lemmas are in the shared layer
  (`Inversion/SignMag.lean`, `Inversion/PackedWords.lean`), stated over the shared word
  operations, so that the x86-64 files carry only the plumbing.
- **M6** replace #10's inversion (str4d's call); docs, CI, README's coverage statements; PR.
- **M7** the termination bound by hull certificate (obligation 5), and the CI step that runs
  the exact re-check of its data: independent of M3–M5, can run in parallel; the PR is not
  merge-ready without it.
- **M8** Aeneas for the portable Rust (stretch).

Draft commits may carry `sorry` where the hole is named here (none at present); the PR that
goes to merge carries none, and CI's axiom census remains the check.

## Aeneas

AeneasVerif/aeneas at `b86120db`, with Charon at its pinned revision, builds through the
repository's Nix flake (`nix build .#charon .#aeneas`; the release bundle's code-signing step
fails on macOS). Its Lean backend pins `leanprover/lean4:v4.31.0` with Mathlib at that tag,
which pasta-asm pins too. `charon cargo --preset=aeneas` on the crate built with
`--cfg pasta_asm_disable`, then `aeneas -backend lean`, translates the portable blocks and the
driver: the trait `InvertBlocks` becomes a record of the six blocks, the driver a function over
it, the blocks straight-line code in Aeneas's `Result` monad, and the fixed loops `loop`
combinators over ranges. Two library functions, `black_box` and `wrapping_neg`, need models.

## Open issues

- The correctness theorem needs `p` prime, for `gcd(p, x) = 1` when `0 < x < p`. CompElliptic
  proves both Pasta primes prime by Pratt certificates, but pasta-asm does not depend on
  CompPoly, so the theorem takes primality as a hypothesis until a certificate is vendored or
  the fact is taken from the consumer.
- Register pressure on x86-64 without `rbp` is not an issue here (the blocks are small), but
  the Apple x86-64 exclusion stays for the multiplication blocks anyway.
- Whether the last round can skip the `v` computation and the `f,g` update as s2n-bignum does
  is a model decision; the outline follows s2n-bignum.
- Constant time is by construction (fixed loops, `csel`/`cmov`, no secret-indexed memory); a
  dudect-style check on the Rust would be a separate, cheap addition.
