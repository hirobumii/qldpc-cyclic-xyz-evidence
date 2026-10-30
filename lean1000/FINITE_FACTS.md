# Residual finite checks

The final proof is kernel checked. Finite computation remains for arithmetic
and binding concrete artifacts, not for enumerating candidate supports,
short cycles, paths, or physical VV/CC edge pairs.

| Location | Finite facts | Role |
| --- | --- | --- |
| Cayley | 30 ordered off-diagonal signed-generator differences for each of A and B are distinct; six generators are distinct and have odd phase | Small arithmetic certificate after symbolic group cancellation; no graph vertices or supports enumerated |
| OrientedLocal | Generator/inverse sign identities; recovery among ten possible block labels | Bind signed-generator labels to physical column block labels |
| Lower | 24 sector/generator/sign phase inequalities | Separate CC ±3 from VV ±1/±7 for X, CC ±7 from VV ±1/±3 for Z |
| CommutationGroup/Concrete | Scalar action laws, generator inverses, 594 sparse row permutations | Instantiate symbolic associativity and product-row orthogonality; no row-pair orthogonality search |
| Symmetry | Unit and inverse identities over the 100 group elements | Concrete group-coordinate identities used in symbolic cancellation and endpoint formulas |
| Binding/Bulk | Row recipes, support-mask equalities, full/stored membership, transpose and bounds | Connect literal stored matrices to actual 101-row block maps, including the derived marker |
| LocalGraph/LocalFormula | Kinds, column endpoint formulas and short neighbor lists | Concrete incidence/coordinate bindings; neighbor facts remain available but the distance argument no longer uses neighbor search |
| Lower | Marker and outside-block column properties | Coordinate properties of the literal incidence maps |
| Distance | Two given witness kernels, dual-separator kernels, weights and pairings | Establish explicit logical representatives of weight six and nonmembership in stabilizer spans |

All these are Lean `decide`/reduction proofs or consequences of proved generic
bridges. No `native_decide` or generated native-evaluation axiom remains.
The arbitrary-support lower bound is symbolic: marker parity leaves sizes two
and four; generic atom pairing, edge injectivity and no rectangles rule them
out. Disconnected supports are included without a connectedness premise.

The 30-value difference certificate is the explicit finite presentation of the
specific generators' algebraic separation; it is not a test of cycles in the
100-vertex graphs. The phase nonedge certificate contains no physical columns
or vertices. Literal table checks do enumerate entries of the published data,
which is the disclosed concrete-input binding boundary.
