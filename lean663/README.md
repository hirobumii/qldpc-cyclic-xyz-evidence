# Exact distance of the 663-qubit CSS code

Lean 4.19.0 / Std proof for the literal matrices in
[qLDPC Challenge PR #3898](https://github.com/unitaryfoundation/qldpc-challenge/pull/3898).

`Qec663.code663_css_distance_certificate` proves CSS commutation, exact X and
Z logical distances 10, and exact phase-free binary Pauli distance 10 with
union support weight. The theorem has no mathematical hypotheses.

## Proof

The physical support splits into a 39-coordinate CC component and four
156-coordinate slices. The literal check equations and the exact weight
partition are proved in `Qec663Proof/Binding663/Bridge.lean`.

For zero CC, a nonzero slice has classical distance at least 10. Each
classical half4 check retains all 24,371,582 supports of size at most four.
The recursive enumeration coverage, sorting/checker soundness, odd-column
augmentation, and correspondence with actual binary vectors are proved.
The X direction uses B columns; Z uses reflected A columns.

For nonzero CC, invertibility and parity force any hypothetical word below
weight 10 to have two singleton slices. The actual singleton preimage sets
are pairwise disjoint. Explicit weight-10 witnesses give the upper bounds;
dual separating functionals prove nonmembership in the full stabilizer span.

## Replay

Use the pinned Lean 4.19.0 `lean` and `lake` on PATH:

```sh
python3 generate_candidate.py --check
python3 check_binding.py
python3 replay.py --fresh
```

`replay.py` builds modules sequentially, runs `lake build`, and checks the
complete final axiom lists through `Audit.lean`. It uses Python's standard
library and Lean's bundled Std; no Mathlib or Python packages are required.
`bootstrap_lean.sh` can install the pinned official release locally.

The final axioms are `propext`, `Classical.choice`, `Lean.ofReduceBool`, and
`Quot.sound`. Native finite computations use `native_decide`; compiler and
runtime correctness are part of the trust boundary. There is no `sorryAx`
or custom distance axiom. `source-build-receipt.json` records the source-only
clean build and hashes; `axioms.txt` records its theorem audit.

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
