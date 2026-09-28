# Correctness of the half-delta divstep Montgomery inverse, on paper

The pen-and-paper argument behind the Lean development under `lean/PastaAsm/Inversion/`; the
plan it belongs to is [constant-time-inversion.md](constant-time-inversion.md), and the lemma
numbers here are the ones that the Lean docstrings cite.

Produced 2026-09-27 by a Claude Fable 5.1 agent; every quantitative claim was first checked
numerically for both Pasta primes, and the bound theorem is cited, not reproved, here.
Notation: `p` is one of the two Pasta primes, so `p` is odd and `2^254 < p < 2^255`.
`R = 2^256`. All congruences are modulo `p` unless said otherwise. Powers of two are invertible
modulo `p`, so dividing by `2^k` in a congruence is legitimate.

## 1. Divsteps

The state is `(d, f, g)` with `d` an odd integer (`d = 2δ`, so `δ ∈ ℤ + ½`; the start is
`d = 1`, that is `δ = ½`), `f` odd, `g` any integer.

    divstep (d, f, g) =
      (2 − d, g, (g − f) / 2)          if d > 0 and g odd
      (2 + d, f, (g + (g mod 2) f) / 2) otherwise

Both divisions are exact: in the first case `g − f` is even because both are odd; in the
second, `g + (g mod 2) f` is even in either parity of `g`. Write `(d_n, f_n, g_n)` for `n`
steps from `(d_0, f_0, g_0)`.

**Lemma 1 (linearity).** There are integer matrices `T_i` with
`(f_{i+1}, g_{i+1})ᵀ = ½ · T_i · (f_i, g_i)ᵀ`, namely `T = [[0, 2], [−1, 1]]` in the swap case
and `T = [[2, 0], [b, 1]]`, `b = g_i mod 2`, otherwise. Hence with `M_n = T_{n−1} ⋯ T_0`,

    2^n · (f_n, g_n)ᵀ = M_n · (f_0, g_0)ᵀ.

Write `M_n = [[u_n, v_n], [q_n, r_n]]`. `M_0 = I`.

**Lemma 2 (locality).** `d_n` and `M_n` depend only on `d_0`, `f_0 mod 2^n`, and `g_0 mod 2^n`.
*Proof.* Induction on `n`. The branch taken at step `i` depends on `d_i` and `g_i mod 2`. If
`(f_i, g_i) ≡ (f_i', g_i') (mod 2^k)` with `k ≥ 1`, the same branch is taken and
`(f_{i+1}, g_{i+1}) ≡ (f_{i+1}', g_{i+1}') (mod 2^{k−1})`, because each new component is half
of a combination of the old ones. So `n` steps from states congruent modulo `2^n` take the same
branches, and the branches determine `d_n` and `M_n`. ∎

**Lemma 3 (bounds).** For every `n`: `|u_n| + |v_n| ≤ 2^n` and `|q_n| + |r_n| ≤ 2^n`; moreover
each entry lies in `(−2^n, 2^n]`; and `max(|f_n|, |g_n|) ≤ max(|f_0|, |g_0|)`. *Proof.* Row
sums: in the swap case the new first row is `2 · (q, r)` and the new second row is
`(q − u, r − v)`; in the other case the new first row is `2 · (u, v)` and the new second row is
`(q + b u, r + b v)`. Each new row sum is at most twice the larger old row sum. The half-open
range: build `M_n` from the left, `M_{n+1} = T_n M_n`, so with `M_n = [[u, v], [q, r]]` the new
entries are `2q, 2r, q − u, r − v` in the swap case and `2u, 2v, q + b u, r + b v` otherwise.
If every old entry lies in `(−2^n, 2^n]`, then each new entry is twice an old one, or an old
one plus or minus another, so it lies in `(−2^{n+1}, 2^{n+1}]`; the strict lower bound and the
closed upper bound both propagate, and the base case is the identity. The `max` bound:
`f_{i+1}` is one of `f_i`, `g_i`, and `|g_{i+1}| ≤ (|f_i| + |g_i|) / 2`. ∎

**Lemma 4 (gcd and the end state).** `gcd(f_n, g_n) = gcd(f_0, g_0)` and `f_n` is odd. If
`g_n = 0` then `f_n = ± gcd(f_0, g_0)`. If `g_0 = 0` then every step is the non-swap case with
`b = 0`, so `f_n = f_0`, `g_n = 0`, and `M_n = [[2^n, 0], [0, 1]]`.

**Lemma 4′ (the adjugate).** Each `T_i` has determinant `2`, so `det M_n = 2^n`, and the
adjugate of Lemma 1 gives `f_0 = r_n f_n − v_n g_n` and `g_0 = u_n g_n − q_n f_n` exactly
(multiply the two identities of Lemma 1 by the cofactors and cancel `2^n`). Hence if `g_n = 0`
then `f_n` divides both `f_0` and `g_0`; with `gcd(f_0, g_0) = 1` that makes `f_n = ±1`. This
is the form the Lean development proves and Theorem 12 uses; the gcd invariance of Lemma 4 is
the classical statement and is not needed separately.

**Theorem 5 (termination; Bernstein et al. 2026, Theorem 1, HOL Light).** If `d_0 = 1`, `f_0`
is odd, `0 ≤ g_0 ≤ f_0 < 2^b`, and `n ≥ ⌈(9437 b + 1) / 4096⌉`, then `g_n = 0`. For `b = 256`
this is `n = 590`. In this development it enters as a hypothesis of the top-level theorem until
it is proved in Lean.

## 2. Divsteps on packed words

Fix a batch length `k ≤ 20` and starting values `f, g` (only their low 20 bits will be used).
Define the packed words

    w_f = (f mod 2^20) − 2^41 · 1 − 2^62 · 0,    w_g = (g mod 2^20) − 2^41 · 0 − 2^62 · 1,

as integers, and run the divstep recurrence on the pair `(w_f, w_g)` with the same branch rule,
reading `g`'s parity from `w_g` and using exact halving.

**Lemma 6 (packing).** After `j ≤ k` steps the packed words are

    w_f^{(j)} = φ_j − 2^{41−j} u_j − 2^{62−j} v_j,   w_g^{(j)} = γ_j − 2^{41−j} q_j − 2^{62−j} r_j,

where `(φ_j, γ_j)` is the state reached from `(f mod 2^20, g mod 2^20)` by the true recurrence
and `M_j = [[u_j, v_j], [q_j, r_j]]` is the true matrix (Lemma 1) for the same branches. The
branches taken on the packed words are the true branches, `|φ_j|, |γ_j| < 2^20`, and
`|w^{(j)}| < 2^63`. *Proof.* Induction on `j`. The coefficient terms are multiples of
`2^{41−j} ≥ 2^21`, so `w_g^{(j)} ≡ γ_j (mod 2^21)` and the parity test on `w_g` reads the
parity of `γ_j`, which by Lemma 2 is the parity of `g_j`; so the branch is the true one. The
recurrence is linear and the matrices update as in Lemma 1, so the packed combination before
halving is `(γ_j ∓ φ_j) − 2^{41−j}(q_j ∓ u_j) − 2^{62−j}(r_j ∓ v_j)` (or with `b`), and every
term is even (the true components are even by exactness, and the coefficient terms carry the
factor `2^{41−j}` with `j < 41`), so exact halving gives the claimed form with `j + 1`.
Magnitudes: `|φ|, |γ| ≤ 2^20 − 1` by Lemma 3's `max` bound applied to the truncated start;
`2^{41−j} |u_j| ≤ 2^41` and `2^{62−j} |v_j| ≤ 2^62` by Lemma 3, so
`|w| < 2^20 + 2^41 + 2^62 < 2^63`. ∎

**Lemma 6′ (the sum does not wrap).** For `j < k`, `|w_g^{(j+1)}| < 2^62`. So the word
`w_g^{(j)} ∓ w_f^{(j)}` (or `w_g^{(j)}` alone) that a step halves, which is `2 w_g^{(j+1)}`, is
below `2^63` in magnitude and fits a signed 64-bit word. An implementation on machine words needs
this, and Lemma 6's bound `|w| < 2^63` does not give it. *Proof.* By Lemma 1 applied to the packed
start, `2^{j+1} w_g^{(j+1)} = q' w_f^{(0)} + r' w_g^{(0)}`, where `(q', r')` is the second row of
the packed run's matrix after `j + 1` steps, which is `M_{j+1}` by Lemma 6; so
`|q'| + |r'| ≤ 2^{j+1}` and `r' ∈ (−2^{j+1}, 2^{j+1}]` by Lemma 3, while `|w_f^{(0)}| ≤ 2^41` and
`|w_g^{(0)}| ≤ 2^62`. Hence `|2^{j+1} w_g^{(j+1)}| ≤ 2^41 |q'| + 2^62 |r'|`, which is below
`2^62 · 2^{j+1}` unless `q' = 0` and `r' = 2^{j+1}`. That row is the second row of `T_j M_j`, so
`r'` is `r_j − v_j`, `r_j`, or `r_j + v_j`; it equals `2^{j+1}` only in the last case, with
`r_j = v_j = 2^j`, and then `q' = q_j + u_j` while `det M_j = u_j r_j − v_j q_j = 2^j (u_j − q_j)`
equals `2^j`, so `u_j − q_j = 1` and `q' = 2 q_j + 1 ≠ 0`. In every case
`2^41 |q'| + 2^62 |r'| ≤ 2^62 · 2^{j+1} − 2^62 + 2^41`. ∎

**Lemma 7 (unpacking).** From `w_f^{(k)}`, with
`t = −w_f^{(k)} = 2^{41−k} u_k + 2^{62−k} v_k − φ_k` and `|φ_k| < 2^20 ≤ 2^{40−k}`:
`⌊(t + 2^{40−k}) / 2^{41−k}⌋ = u_k + 2^21 v_k` exactly, and then
`v_k = ⌊(u_k + 2^21 v_k + 2^20 − 1) / 2^21⌋`, `u_k = (u_k + 2^21 v_k) − 2^21 v_k`, using
`u_k ∈ (−2^20, 2^20]` from Lemma 3. Likewise for the second row from `w_g^{(k)}`. (The
half-open range is what makes this well defined: `(2^20, 0)` and `(−2^20, 1)` pack
identically.)

**Corollary 8 (`divstep59`).** With `M^{(1)}` from 20 packed steps at `d`, `M^{(2)}` from 20
packed steps at `d'` on the state `2^{−20} M^{(1)} (f, g)` (whose low 20 bits are determined by
the low 40 bits of `(f, g)`, so by the low words), and `M^{(3)}` from 19 steps likewise, the
product `M^{(3)} M^{(2)} M^{(1)}` is the true 59-step matrix `M_59` and the returned `d` is
`d_59`, by Lemma 2 applied three times. Entries of `M_59` lie in `(−2^59, 2^59]`, of the
partial products in `(−2^40, 2^40]`, so all fit signed 64-bit words, and the intermediate
states' low words can be recomputed from the low words of `(f, g)` alone.

## 3. The round arithmetic

Throughout the rounds `|f|, |g| ≤ p < 2^255` (Lemma 3's `max` bound from `(p, x)`), and
`0 ≤ u, v < 2^256` (Lemma 10 below).

**Lemma 9 (`updateFG`).** `m00 f + m01 g` and `m10 f + m11 g` are divisible by `2^59` (Lemma
1), and `|m f + m' g| ≤ (|m| + |m'|) · max(|f|, |g|) < 2^59 · 2^255 = 2^314`, so both fit in
five signed words and the shifts are exact.

**Lemma 10 (`amontred`).** Let `t = m00 u + m01 v` (or the second row), so
`|t| ≤ (|m00| + |m01|) · max(u, v) < 2^59 · 2^256 = 2^315`. Let `s = t + 2^61 p`. Then
`s ≥ 2^61 · 2^254 − 2^315 = 0`, and `s < 2^315 + 2^61 · 2^255 = 2^315 + 2^316 < 2^317`. Let
`w = (s · inv) mod 2^64` where `inv = −p^{−1} mod 2^64`; then `s + w p ≡ 0 (mod 2^64)` and

    t' = (s + w p) / 2^64 < s / 2^64 + p < 2^251 + 2^61 p / 2^64 + p = 2^251 + 9p/8.

In integers, `8 t' < 2^254 + 9p`, which is the form the Lean statement uses. Since
`p > 2^251 · 8/7`, this is below `2p`; and `2^251 + 9p/8 < 2^256` since `p < 2^255`. Also
`t' ≡ t · 2^{−64} (mod p)`. So `amontred` returns a four-word value below `2^256` congruent to
`t / 2^64`, and one conditional subtraction of `p` makes it canonical. (s2n-bignum's P-256
version needs a top-carry check inside `amontred`; the Pasta bound shows none is needed, but a
transcription may keep the instruction if it is harmless.)

Note the starting `v = 2^562 mod p < p < 2^256` and `u = 0` satisfy the range, and Lemma 10
keeps it.

## 4. The invariant and the result

Let `(f_i, g_i)` be the true state after `59 i` divsteps from `(p, x)` with `d_0 = 1`, and let
`(u_i, v_i)` be the coefficient vector after `i` rounds: `u_0 = 0`, `v_0 = 2^562 mod p`, and
`(u_{i+1}, v_{i+1}) = (amontred (m00 u_i + m01 v_i), amontred (m10 u_i + m11 v_i))` with
`M = M_59` of round `i + 1`.

**Lemma 11 (invariant).** `(f_i, g_i) ≡ x · 2^{5i − 562} · (u_i, v_i) (mod p)`. *Proof.*
`i = 0`: `(p, x) ≡ (0, x) = x · 2^{−562} · (0, 2^562)`. Step: by Lemma 1,
`(f_{i+1}, g_{i+1}) = 2^{−59} M (f_i, g_i) ≡ 2^{−59} M · x 2^{5i − 562} (u_i, v_i)`, and by
Lemma 10 `(u_{i+1}, v_{i+1}) ≡ 2^{−64} M (u_i, v_i)`, so the right side is
`x · 2^{5i − 562 − 59 + 64} (u_{i+1}, v_{i+1}) = x · 2^{5(i+1) − 562} (u_{i+1}, v_{i+1})`. ∎

**Theorem 12 (correctness).** Assume Theorem 5 for `b = 256` and `0 < x < p`. After ten rounds
(590 divsteps) `g_10 = 0`, so `f_10 = ±1` by Lemma 4 (`gcd(p, x) = 1`). By Lemma 11 with
`i = 10`, `f_10 ≡ x · 2^{−512} u_10`, hence `x · (f_10 · u_10) ≡ 2^512 (mod p)`. The
implementation's last round computes `u_10` with the sign of `f_10` folded into the matrix row,
then reduces strictly; by Lemma 10 one conditional subtraction gives the canonical
`z ≡ f_10 u_10`, and `x z ≡ R^2`. In Montgomery terms, if `x = X R` and `z = Z R` then
`X Z ≡ 1`.

For `x = 0`: by Lemma 4 every matrix is `[[2^59, 0], [0, 1]]`, so `u` stays `0` through every
round and `z = 0`.

**The sign of `f_10` from one word.** The implementation reads the sign from
`(m00 f_9 + m01 g_9) mod 2^64` (the low word of `2^59 f_10 = ±2^59`, before the shift): as a
signed 64-bit word, `+2^59` has bit 63 clear and `−2^59` has it set. This uses only that the
low word of the five-word product is the low word of the true integer, which Lemma 9 gives.

## 5. What is not covered here

The bound (Theorem 5) and the block-level equalities between each `asm!` block's transcription
and the word-level functions of §2–§3. The former is proved in Lean from Bernstein's hull
certificate, following Harrison's HOL Light argument (`HullBound.lean`, with the data in
`HullData.lean` and the checks in `HullCert.lean`; the plan's obligation 5 describes the
certificate). The latter are the per-ISA obligations that the skeleton generator and its proofs
handle, as for the existing blocks. The primality of `p`, which Theorem 12 needs for
`gcd(p, x) = 1`, is taken as a hypothesis.
