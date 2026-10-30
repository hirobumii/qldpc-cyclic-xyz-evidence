# Credits and provenance

## Original code and logical witnesses

The literal `[[1000,406,6]]` CSS matrices, the group-algebra construction and
the two weight-six logical witnesses are from **@hirobumii**'s
[qLDPC Challenge PR #3863](https://github.com/unitaryfoundation/qldpc-challenge/pull/3863).
The published input is preserved byte-for-byte in `source.json`, including
its original author and model provenance. The exact source hashes are in
[README.md](README.md).

## Structural distance proof: Henryk Soboń

**Henryk Soboń** supplied the structural distance argument establishing
`dX = dZ = d = 6` for this fixed code. The source used here is his
[public proof package at revision 15116a45b995600a7a28e677d8617afabf1fe025](https://github.com/henryksobon300-code/my-work-henryk-sobon/tree/15116a45b995600a7a28e677d8617afabf1fe025/research/qldpc-1000-406-d6).
His classification by the number of CC coordinates is the mathematical
starting point and remains the global structure of this formalization.

## Algebraic adaptation and Lean formalization

This development specializes Soboń's CC-support argument using the phase
bipartition. It replaces the local support and short-cycle searches, path
bounds and physical VV/CC pair comparisons with symbolic bipartite-graph,
Cayley-group and phase-separation proofs. Concrete generator arithmetic and
matrix/witness bindings remain as kernel-checked finite facts, inventoried
in [FINITE_FACTS.md](FINITE_FACTS.md).

The formalization additionally supplies the literal-matrix binding,
full/stored kernel equivalence, algebraic CSS commutation, exact sector
minima, physical Pauli union-support distance and reproducible axiom audits.
Its binary-vector, row-span and support infrastructure was adapted from
[this repository's prior Lean 663-coordinate development](../lean663/).

**@hirobumii** maintains and publishes this evidence package. AI assistance
was used throughout: a **GPT-6 Astra subagent** implemented the Lean
formalization and algebraic replacements; the **primary OpenAI Codex agent**
reviewed the mathematics and definitions, independently rebuilt the project,
audited source binding and dependencies, and prepared the publication and
replay checks. These tool roles are recorded separately from the original
code and mathematical-proof contributions.

## Third-party material

`source.json` is reproduced from the qLDPC Challenge repository. Its Apache
2.0 license notice is retained in
[THIRD_PARTY_LICENSE_APACHE_2.0.txt](THIRD_PARTY_LICENSE_APACHE_2.0.txt).
The original mathematical proof is cited above; the Lean proof development
here is the documented formalization and adaptation of that argument.
