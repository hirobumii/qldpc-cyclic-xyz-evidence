# Exact distance of the 663-qubit CSS code

Lean 4.35.0 / Std proof for the literal matrices in
[qLDPC Challenge PR #3898](https://github.com/unitaryfoundation/qldpc-challenge/pull/3898).

`Qec663.code663_css_distance_certificate` proves CSS commutation, exact X and
Z logical distances 10, and exact phase-free binary Pauli distance 10 with
union support weight. The theorem has no mathematical hypotheses.

## Proof

The physical support splits into a 39-coordinate CC component and four
156-coordinate slices. The literal check equations and the exact weight
partition are proved in `Qec663Proof/Binding663/Bridge.lean`.

For zero CC, a nonzero slice has classical distance at least 10. The full
half4 proposition still covers all 24,371,582 supports of size at most four.
Its proof now uses cyclic translation within the four 39-coordinate blocks.
`OrbitCoverage.lean` proves that every support has a representative in the
anchored enumeration; no orbit count is assumed as a proof premise.
`OrbitSound.lean` proves that distinct minimum-rotation syndrome keys and
syndrome-stabilizer containment imply injectivity on every translated support.
`EnumerationNodup.lean` then recovers the original exhaustive Boolean check
without evaluating its full list. Odd-column augmentation and correspondence
with actual binary vectors are unchanged. X uses B columns; Z uses reflected A.

`OrbitChecks.lean` binds all three concrete column tables (A, B, reflected A)
to this reduction. The column bindings and cyclic equivariance use kernel
proofs; only the reduced finite checks use `native_decide`. Stabilizer tests
include periodic supports and the empty support. Executable regressions
reject the constant-syndrome singleton and accept the empty support.
The implementation generates 966,356 anchored supports and keeps 624,916
representatives (counts by weight: 1, 4, 310, 15,916, 608,685). These counts
describe the computation; coverage follows from the structural proof.

For nonzero CC, invertibility and parity force any hypothetical word below
weight 10 to have two singleton slices. The actual singleton preimage sets
are pairwise disjoint. Explicit weight-10 witnesses give the upper bounds;
dual separating functionals prove nonmembership in the full stabilizer span.

## Replay

Use the pinned Lean 4.35.0 `lean` and `lake` on PATH:

```sh
python3 generate_candidate.py --check
python3 check_binding.py
python3 replay.py --fresh
```

`replay.py` builds modules sequentially, runs `lake build`, and checks the
complete final axiom lists through `Audit.lean`. It uses Python's standard
library and Lean's bundled Std; no Mathlib or Python packages are required.
`bootstrap_lean.sh` can install the pinned official release locally.
Lake precompiles imported modules so the finite checks execute their compiled
functions. This does not change the stated native computation trust boundary.

The standard axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Lean 4.35 records each `native_decide` computation with its own generated
evaluation axiom. `replay.py` checks exact per-theorem dependency lists;
`Audit.lean` also prints the types of the native evaluation axioms. Compiler
and runtime correctness remain part of the trust boundary. There is no `sorryAx`
or custom distance axiom. `source-build-receipt.json` and `axioms.txt` retain
the historical Lean 4.19.0 clean-build receipt and theorem audit. Each new
replay writes its current results to `LAST_REPLAY.json` and `build-logs/`;
these generated files are not committed.

## Matrix binding

`data/candidate.json` is the actual submitted JSON. `generate_candidate.py`
reproduces the complete Lean literal matrix module byte for byte;
`check_binding.py` also compares every literal row and witness independently.
The canonical CSS checks SHA256 is
`98f34742a2c089d3797bdef1aa1b7d4cec19615bc72009947356edfc2c4fdc8f`.
JSON parsing and SHA256 are external transcription checks. Lean proves the
distance statement for the literal finite matrices. Rank/k and signed
Hilbert-space semantics are separate from this distance theorem.

Model attribution: GPT-6 Astra + GPT-6.1 Sol.
