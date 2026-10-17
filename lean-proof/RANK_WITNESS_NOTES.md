# Kernel-checked rank and nontrivial logical certificates

## Established statements

- `QLDPC.Candidates.l7_rank`: the exact 56-qubit input generator span has a binary basis of size 32.
- `QLDPC.Candidates.l11_rank`: the exact 88-qubit input generator span has a binary basis of size 52.
- `QLDPC.Candidates.witness7_logical` and `witness11_logical`: the supplied weight-four vectors commute with every generator and are not in the full generator span.
- `l7_nontrivial_weight_four` and `l11_nontrivial_weight_four` package these vectors as existential upper-bound witnesses.
- `l7_unique_coordinates` and `l11_unique_coordinates`: every vector in each original generator span has exactly one coefficient function on `Fin 32` / `Fin 52` in the certified basis.
- `l7_recover_coefficients` and `l11_recover_coefficients`: pivot-coordinate extraction recovers every coefficient, for arbitrary coefficient functions.

## Why the dimension statements are semantic

`InSpan S` is the inductive closure of the original generators under zero and componentwise binary XOR. `linComb B c` is an actual finite binary sum of the basis vectors, selected by Boolean coefficients.

`IsBinaryBasis S B` has two propositions:

1. The original span and the span of `List.ofFn B` are equal for every Pauli vector.
2. Every coefficient function whose linear combination is zero is identically false.

Both implications of span equality are proved using explicit XOR certificates: each basis row is a combination of original rows, and every original row is a combination of basis rows. Independence follows from a kernel-checked identity pivot submatrix and a generic theorem showing that these coordinates recover every coefficient. The proof does not enumerate coefficient functions and does not equate an unverified Gaussian-elimination output with dimension.

`RankCoordinates.lean` additionally proves that closure-based span membership is equivalent to existence of an actual coefficient expansion, and derives unique coordinates for every span vector. Thus the certified basis parametrizes the full span by exactly 32 or 52 freely chosen binary coefficients.

## Nonmembership certificate

For L=7 or 11, the dual vector is pure X on all sheets of cube blocks 000 and 010:

- L=7: X support 0 through 6 and 14 through 20.
- L=11: X support 0 through 10 and 22 through 32.

Every original generator commutes with this dual. The supplied pure-Z weight-four logical anticommutes with it. `span_annihilator` proves by induction on the actual span definition that all span vectors commute with any common orthogonal, ruling out membership of the logical witness even after arbitrary generator rebasing.

## Files and reproducibility

- `QLDPC/Rank.lean`: generic finite binary combination, span equality, basis, coefficient-recovery, and symplectic-annihilator theorems.
- `QLDPC/RankCoordinates.lean`: coefficient existence and uniqueness.
- `QLDPC/RankData.lean`: explicit basis masks, pivot positions, bidirectional change-of-generator certificates, and dual vectors.
- `QLDPC/RankWitness.lean`: closed finite certificate proofs and rank/logical-witness theorems.
- `QLDPC/RankSemantic.lean`: final unique-coordinate and recovery corollaries.
- `generate_rank_certificates.py`: untrusted certificate generator. Its outputs are checked by Lean; it is not an axiom or part of the trusted proof kernel.

The certificate file imports the exact input candidate literals from `QLDPC/Candidates.lean`, whose support-list bindings are independently checked there. This component neither edits the source candidates nor changes the repository trusted verifier.

With the installed official Lean 4.19.0 toolchain:

```
source env.sh
lake build QLDPC.RankSemantic
```

All finite closed certificates use kernel-rechecked `decide`. No `sorry`, `admit`, custom axioms, `native_decide`, or `ofReduceBool` is used. The rank and logical witness theorem axiom reports contain only Lean's standard `propext` and `Quot.sound`; unique-coordinate theorems also use the same standard axioms.

The statements here concern the finite binary symplectic stabilizer data. They do not themselves formalize complex Hilbert spaces, signed Pauli matrices, or the general quantum stabilizer-code dimension theorem.
