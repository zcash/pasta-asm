# Inversion proof status and layout

## Public contract (fixed while proofs are developed)

`PastaAsm/{AArch64,X86_64}/Entry.lean` contains identical
`invert_entry_spec` statements and proof bodies. They specialize the respective
`Spec/Invert.lean` theorem `invert_spec` to the Boolean canonical-input check.

The contract is restricted to the actual Pallas and Vesta fields by
`IsInversionField`. `PastaField` alone records a modulus shape and Montgomery
constant, not primality. The result is bounded and canonical. Zero returns zero;
otherwise `value * result ≡ R² (mod p)` for the Montgomery-encoded input/output.
There are no convergence or coefficient-bound assumptions in this contract.

The two top-level `invert_spec` proofs intentionally contain `sorry` while this
branch is developed. These are visible obligations, **not verified correctness**.
Intermediate commits may contain them as authorized by the maintainer; before
merge there must be no `sorry`, `native_decide`, or new axioms, and the strict
proof-coverage and independent-kernel checks must pass.

## Layout

- `Semantics`, generated `Transcription`, and `Compositions` keep their established
  architecture roles.
- `Spec/Invert.lean` states the top-level architecture-specific obligation.
- `Spec/Invert/*.lean` contains arithmetic and composition proofs.
- `Spec/Invert/Divsteps/*.lean` contains loop arithmetic, approximation-window
  correspondence, and checked round proofs. These are separated where their
  dependency structure or elaboration cost warrants it.
- `Inversion*.lean` at the shared level contains architecture-independent state,
  prime certificates, coefficient/normalization arithmetic, and convergence
  lemmas. These are supporting results, not an implicit end-to-end theorem.
- Generated `InvertVectors.lean` checks all 34 distinct canonical corpus inputs
  on each backend. Inputs come from the existing corpus; expected inverses are
  independently calculated, **not inversion hardware captures**.

## Remaining obligations

- Complete the AArch64 `mulSigned`, `updateAB`, `normalizeCoefficient`, and
  `divsteps31` wrapper proofs. The generator's `UNPROVED_ROUTINES` is the
  machine-checked inventory of missing block proofs.
- Complete the near-length approximation progress proof and connect both length
  cases to the actual fifteen batches and final 47-step tail.
- Establish the asymmetric selected-coefficient bound required by normalization.
- Compose these results with the existing Montgomery and addition proofs to
  discharge both fixed `invert_spec` obligations.

## Checks

From the repository root, `lean/scripts/check.sh` verifies generation, registered
skeletons, explicit missing-proof accounting, and Python validation tests.
`gen.py --check-specs --strict` additionally rejects missing block proofs.
From `lean/`, `lake build` checks the current development and reports the expected
`sorry` warnings. `lake build --wfail` is the merge-ready requirement, not a claim
made for placeholder-bearing commits. Root imports must cover all retained
project modules; files outside that closure are not validated by a root build.

## Recovery material

Before stabilization, the complete non-cache worktree, Git history bundle, and
working/index patches were preserved outside the repository at
`/tmp/pasta-invert-recovery-2OUDss`. Its `quarantine/` preserves original relative
paths for unfinished proofs, scratch modules, skeleton sidecars, logs, Python
bytecode, loose Lake experiments, and old validation checkout trees. Nothing was
silently discarded. This location is local recovery material, not a build input;
`/tmp` is not durable storage and should be copied elsewhere if long-term retention
is needed.

The quarantined near-length and AArch64 signed-multiplication/31-wrapper drafts
are incomplete and must not be reintroduced as verified modules without focused
compilation and skeleton checks. The experimental signed-multiplication
phase-clearing generator changes are not part of the stabilized pipeline.
