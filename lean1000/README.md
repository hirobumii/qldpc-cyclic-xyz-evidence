# Exact CSS distance of the literal PR3863 code

This Lean 4.35.0 / Std-only project proves the unconditional statements
`Qldpc1000.dX_eq_six`, `dZ_eq_six`, `d_eq_six`, and `exact_distance` for the
published 1000-coordinate CSS matrices, with **no native-evaluation axioms**.
The three distances are genuine least
weights over logical operators, not constants defined to be six.

The combined theorem `Qldpc1000.certified_public_code` additionally includes
CSS commutation and equality of the stored 297-row and expanded 300-row kernels.
The rank/dimension claim k=406 was checked independently in the preceding
review, but is **not a formal theorem of this project**.

## Attribution and source binding

The code and weight-six X/Z logical witnesses are from hirobumii's public
[qLDPC Challenge PR3863](https://github.com/unitaryfoundation/qldpc-challenge/pull/3863).
The structural distance-proof strategy is Henryk Soboń's
[public proof](https://github.com/henryksobon300-code/my-work-henryk-sobon/tree/15116a45b995600a7a28e677d8617afabf1fe025/research/qldpc-1000-406-d6).
This formalization specializes his CC-support case split using the verified
bipartition. Local incidence exclusions are proved by symbolic bipartite
graph and Cayley-group arguments, without support or short-cycle searches. The underlying binary-vector, row-span and support
lemmas were adapted from the prior [663-coordinate proof project](../lean663/).
See [CREDITS.md](CREDITS.md) for the mathematical attribution and formalization roles.

`source.json` is the exact 49,594-byte challenge file at commit
`9587d1aa54e98aa49caacf4a2cb358424e70160e`, path `codes/1000-406-6.json`:

- SHA-256: `fdc1e71bfd9a588b39f545882a93b5b316582ecdd157451bd03c7411219b842b`
- Git blob: `1492412cf38995f2d0d9507ad0402a260a28b3fb`

`Data.lean` contains the literal published sparse rows. `generate_data.py`
generates these literals and auxiliary certificates. Python is not a proof
oracle: Lean checks all certificate semantics. Matching the external JSON
bytes to the literal theorem input is an artifact-binding check; the Lean
theorem is about those literal matrices, not about a network resource or a
formal SHA-256/parser theorem. The root reviewer independently parsed and
compared every generated literal against the frozen JSON and reconstructed
matrices without executing this generator.

## Proof architecture

- `Core.lean`, `VectorFacts.lean`, `MaskBridge.lean`, `Support.lean`: real
  `Fin 1000 → Bool` vectors, binary dot products, inductive stabilizer spans,
  exact physical Hamming support, finite linear maps, and bounded-mask bridges.
- `Sparse.lean`: elementary XOR syndromes, removal and congruence lemmas.
  The former recursive rejection checker and its soundness proof are removed.
- `SmallGraph.lean`: a generic simple bipartite graph with no four-cycle has
  no nonempty even-edge zero-incidence support of size at most five. Two edges
  would coincide; four edges pair on each shore and give a duplicate or a
  rectangle. The argument has arbitrary symbolic edges and vertices and
  includes disconnected supports.
- `Shores.lean`: linear projections to the two shores turn zero incidence
  into two zero atom sums, with explicit bounds on decoded masks.
- `Cayley.lean`: group cancellation reduces two common neighbors to equality
  of ordered signed-generator differences. The 30 non-diagonal differences
  for each of A and B are distinct by a small generator-arithmetic certificate.
  Odd phase increments give the bipartition for arbitrary vertices.
- `OrientedLocal.lean`: orient actual edges by phase parity; prove physical
  edge injectivity and absence of rectangles, then instantiate the generic
  small-edge theorem. CC single-generator graphs are subgraphs of the same
  A/B Cayley graphs, so the argument covers them too.
- `PhaseNonedge.lean`: complementary shore projections recover endpoints
  from equal boundaries. Symbolic phase cancellation then separates the
  designated CC edge from all VV edges: X uses CC ±3 versus VV ±1/±7; Z uses
  CC ±7 versus VV ±1/±3. Only generator/sign arithmetic is checked finitely.
- `Structural.lean`: the global CC-count argument. Partition support into
  three VV blocks and CC. Bipartition gives `s_b ≡ t (mod2)`. The cases t=0,
  t=1, and t>=2 close using local VV/CC exclusions and a designated CC nonedge.
  No global 1000-qubit support enumeration is used.
- `Bulk.lean`: sequential table-check semantics, sparse support-mask decoding,
  and a proved bitwise transpose. Bounds on both zipped tables prevent silent
  truncation from omitting a required entry.
- `Binding.lean`: every full block row and marker row is an explicit sum of
  stored literal rows. The marker is a genuine derived parity check, with
  no extra parity assumption. Its recipe uses the 50 even-phase retained rows,
  equal to the odd-phase full-row sum. All 101-bit columns are checked against
  these actual linear maps. Full/stored kernel equivalence is also proved.
- `LocalGraph.lean` and `LocalFormula.lean`: bind actual sparse row incidence
  to short neighbor lists and explicit two-endpoint group-graph columns.
  All finite bindings use kernel reduction and proved table-lookup semantics.
- `Symmetry.lean`: group inverses and coordinate identities used by the
  explicit endpoint formulas. The former orbit/representative search modules
  are removed from active sources.
- `Lower.lean`: discharges every structural premise for both sectors. The
  actual derived marker bit forces even local support; algebraic VV/CC
  exclusions and phase-separated nonedges complete the global case argument.
- `Distance.lean`: literal weight-six witnesses, dual-separator nonmembership
  in stabilizer spans, true sector minima, and mixed Pauli union support.
  Y occupies one physical site; both components of every mixed Pauli are
  covered by the proved kernel lower bounds.
- `Audit.lean`: combined certificate and complete transitive axiom reports.
- `CommutationGroup.lean`: symbolic associativity of the semidirect product,
  derived from kernel-checked scalar action laws; left/right regular actions
  commute directly by associativity.
- `CommutationAlgebra.lean`: a generic lifted-product row theorem for arbitrary
  commuting bijections. The VV and CC overlap terms cancel in pairs, expressing
  `A_k B_j + B_j A_k = 0` over F2. The qubit indices remain symbolic; rows are
  not enumerated in this algebraic proof.
- `CommutationConcrete.lean`: verifies the generator inverse identities and
  the 594 literal length-eight row permutations by kernel `decide`, then
  specializes the generic theorem. Formula/literal binding is explicitly
  separate from the algebraic commutation argument.

## Trust boundary

There are no unfinished proofs, handwritten axioms, unsafe declarations,
external solvers, unproved Python premises, or private MathemaSpace engine
dependencies. Generic soundness, structural case logic, vector/mask bridges,
witness weights, separator pairings, and **literal CSS commutation including
its source binding** are kernel proofs. `css_commutes` depends only on
`propext`, `Classical.choice`, and `Quot.sound`, with no native-evaluation axiom.

All remaining finite facts now use kernel `decide` with proof-producing
semantic bridges. The complete transitive dependency sets of
`exact_distance`, `css_commutes`, and `certified_public_code` are exactly
`propext`, `Classical.choice`, and `Quot.sound`. They contain **zero**
`native_decide`/native compiler axioms. The native compiler and runtime are
not additional proof oracles for this certificate. The normal trust in the
Lean kernel and its implementation remains; external JSON identity is the
artifact-binding boundary described above.

The exact per-theorem sets are printed by Lean and checked against explicit
allowlists for 38 theorem outputs in `reproduce.py`, with results saved in
`audit.json`. `SearchDependencyAudit.lean` additionally traverses project proof
and type dependencies: neither final certificate depends on `rejects`,
`rejects_sound`, `representative_checks`, or the former `bulk_nonedge` pair
enumeration. This diagnostic is reviewer tooling, not a proof premise. Fresh replay
also runs `lean --trust=0` on the public audit entrypoint. This is a completed
kernel-checked distance certificate, not merely conditional structural lemmas.

The proof retains Soboń's global CC-support classification and replaces local
support/short-cycle searches and physical-edge pair comparisons with
algebraic/combinatorial arguments. The original matrix literals and actual
distance definitions are retained.

Publication of this proof development is separate from acceptance of a
Challenge certificate. Rank/dimension, circuit distance, decoding performance,
and a new code/Pareto point are outside the formal theorem's scope.

## Reproduce from fresh sources

From the repository root, with Lean 4.35.0 available through `elan` or a
toolchain `bin` directory containing `lean` and `lake` on `PATH`:

```sh
cd lean1000
python3 reproduce.py --toolchain-bin "$(dirname "$(command -v lean)")" --out /tmp/qldpc1000-fresh
```

Use a new output directory. The script copies only source files, regenerates
and compares literals byte-for-byte, runs `lake --no-cache build`, a separate
`lean --trust=0` axiom audit and the dependency-closure diagnostic, scans for unfinished
or custom trusted declarations, and saves `build.log` and `audit.json`.
The remaining finite checks are inventoried in `FINITE_FACTS.md`; no support,
short-cycle, or physical-edge pair enumeration enters the final distance proofs.
No network or nonstandard Python packages are required. A normal in-place
build is simply `lake build` with that toolchain.
