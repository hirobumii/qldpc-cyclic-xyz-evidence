# Lean formalization of two finite XYZ stabilizer candidates

This project formalizes the **phase-free binary-symplectic parameters** of the
original 56- and 88-qubit candidate check matrices. It is separate from the
original qLDPC research repository and does not change its trusted validator,
submission files, or confidence metadata. Nothing is published by this project.

## Verified final status

The independent source-only audit passed on 2026-10-17: 59 Lean modules,
61 successful steps, 22 final theorem type/axiom inspections, and six semantic
regression tests. Both main parameter theorems depend exactly on the standard
Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. Final source hashes
match the audited snapshot. See `audit/REVIEW.md`, `audit/final-result.json`, and
`audit/final-build.log`. A Chinese reproduction guide is in `README.zh-CN.md`.

## Main statements

The aggregate module is `QLDPC.Parameters`, also imported by `QLDPC.lean`.

- `QLDPC.xyz56_parameters`: the exact 56-qubit candidate has parameters
  `[[56,24,4]]` in the binary-symplectic sense.
- `QLDPC.xyz88_parameters`: the exact 88-qubit candidate has parameters
  `[[88,36,4]]` in the same sense.
- `QLDPC.xyz56_geometry` and `QLDPC.xyz88_geometry`: respectively 35 and 55
  supplied checks, every check of Pauli weight 8, every qubit of degree 5.

`HasParameters S k d` means `k ≤ n`, pairwise symplectic commutation of all
checks, an actual independent spanning family of size `n-k`, and exact logical
Pauli distance `d`. `HasDistance` includes both a lower bound over **all**
nontrivial logical Paulis and an explicit witness attaining that bound.

## What is formalized

A Pauli is a pair of `BitVec n` values, its X and Z coordinates. Multiplication
modulo global phase is componentwise XOR. A site's weight is one whenever its
X or Z bit is nonzero. Commutation is parity of the usual symplectic product.
The stabilizer row span is an inductively defined closure under zero, original
checks, and XOR, not the output of a Gaussian-elimination program.

### Exact input binding

The original JSONs are copied unchanged under `data/`. `Candidates.lean`
contains their literal X/Z support lists and bit-vector masks. Lean proves the
two representations equal. `Binding.lean` proves every input index is in range,
there are no repeated indices within an axis list, and the witness literals
match the original support lists. `Geometry.lean` also proves equality with the
explicit five-block cyclic cube construction.

The external JSON-to-Lean transcription boundary is independently checked; the
Lean kernel does not itself parse JSON or certify SHA-256. Input hashes:

- L=7: `c598183c0768f29abffb430992543ce3cd7ddbb1337be0701c7db5ad88252c45`
- L=11: `353865b626ea7205b62e5fcf0826b4aa453f506d28330c6291fcf1d8344ffefe`

### Dimension

The explicit bases have 32 and 52 rows. Lean checks both directions of the
change-of-generators certificates and the identity pivot matrices. Generic
proofs show that every vector in the original row span has exactly one binary
coefficient vector in the certified basis. Thus these are semantic dimension
proofs, not just asserted elimination counts.

### Distance at most four

The original pure-Z quartet is proved to commute with every supplied check and
to have weight four. Nonmembership has a particularly transparent certificate:
a pure-X Pauli on every sheet in cube blocks 000 and 010, of weight 2L. It
commutes with every stabilizer generator but anticommutes with the quartet at
one site. Linearity of the symplectic form then rules out the quartet being in
the stabilizer span.

### Distance at least four

A generic Lean proof decomposes an arbitrary Pauli along its nonidentity
support and relates its syndrome to the XOR of the singleton syndromes. The
finite certificate checks that singleton syndromes are nonzero, and that the
XOR of singleton syndromes at distinct sites is neither zero nor another
singleton syndrome. This excludes support sizes one, two and three. The
support decomposition and the completeness argument are proved in Lean;
checking only a finite test set without that bridge would not suffice.

## Trust and scope

The toolchain is pinned Lean 4.19.0 with its bundled Core/Std, with no Mathlib or
other external package. See `TOOLCHAIN.md` for the official source, binary
archive hash, and installation details. Proofs use ordinary kernel-reduced
`decide`. They do not use admitted proofs, custom axioms, `native_decide`, or an
external Boolean result accepted as a theorem. `Audit.lean` prints the axiom
dependencies of the main and supporting statements. `scripts/check_sources.py`
also checks the project sources for prohibited trust escapes.

The standard Lean foundational axioms reported by the final audit are distinct
from custom axioms. Consult the actual saved audit output for the exact lists.

This is a formalization of two **finite binary stabilizer spaces**. It does not
formalize complex Hilbert spaces, the choice of signed Pauli representatives,
or the stabilizer-code realization theorem. An external phase-consistency
check is not a Lean proof of those facts. Nor does this project claim a formal
infinite-family theorem, intrinsic non-CSS theorem, literature novelty, or
optimality. The original JSON confidence fields are left unchanged.

## Reproduce

```sh
./scripts/bootstrap_lean.sh
source env.sh
python scripts/check_sources.py
lake build
lake env lean -j1 Audit.lean
```

The first command downloads only the pinned official Lean release if needed.
The finite certificate files disable asynchronous elaboration so proofs are
checked serially inside each file. On machines with limited memory, avoid
multiple independent full builds at once. The independent audit uses a fresh
source snapshot without copying any project `.olean` files.
