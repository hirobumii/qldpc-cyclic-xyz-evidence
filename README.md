# Cyclic XYZ finite-instance evidence

Public supplementary material for @hirobumii's two Unitary Foundation QEC
Challenge submissions: [[56,24,4]] and [[88,36,4]], with maximum generator
weight eight and five incident checks per data qubit. The cyclic XYZ artifacts are retained in their original directories.

The `lean-proof` directory contains the finite-proof source package, its input
JSON, manifests and independent clean-build audit. The proof inputs and challenge
submissions have identical ordered checks and logical witnesses; provenance
metadata is excluded from that comparison. `supplement/check_binding.py` verifies
the binding and the full-rowspace support-minimality certificate.

## Construction

For L=7 or 11, label the data qubits by (q,s), with q=(q1,q2,q3) in {0,1}^3
in lexicographic order and s in Z/L. The flat index is
L*(4*q1+2*q2+q3)+s. For every i in Z/L, use five checks, each with one
position from every q block:

| Pauli | position in block q |
| --- | --- |
| X | i |
| X | i+q1+2*q2+3*q3 |
| Z | i+q1 |
| Z | i+2*q2+3*q3 |
| Y | i+2*q2 |

All positions are reduced modulo L. The binary symplectic ranks are 32 and
52. A nontrivial weight-four Z operator occupies (010,0), (011,0),
(100,-1), (101,-1). The finite proof package proves commutation, rank,
incidence structure and exact distance in the binary symplectic setting.

## Reproduction and boundaries

Use the pinned official Lean 4.19.0 release and commands in
`lean-proof/README.md` and `lean-proof/TOOLCHAIN.md`. Main theorems are
`QLDPC.xyz56_parameters` and `QLDPC.xyz88_parameters`. The supplied independent
source-only audit completed 61 steps, checking 59 modules, theorem types,
transitive axiom dependencies and semantic regression examples. Its results
are in `lean-proof/audit/final-result.json` and `lean-proof/audit/final-build.log`.
That build was performed before this submission preparation. It has not been
represented as a new kernel build during preparation.

During submission preparation the delivered manifests, source scan, JSON to
Lean literal binding, independent candidate computation and byte-identical
regeneration checks were rerun in a copy. See `supplement/preparation-audit.txt`.
The original delivered directory was preserved unchanged.

JSON parsing, hashes and binding the submitted JSON to source literals remain
external checks. Lean does not formalize the full signed-Pauli/Hilbert-space
correspondence, infinite families, local-Clifford non-CSSness, novelty,
experimental fault tolerance, a syndrome-extraction circuit or a hardware
layout. The finite all-plus phase dependency check is external Python evidence.

At upstream challenge commit 0433d4ff5ff371976c0c03b02b103770f9fe0ee9,
general stabilizer entries remain `upper_bound` and have no circuit tier.
This material is supplemental evidence and does not request a native exact
certificate or alter challenge verifier rules.

For both finite codes, every supplied generator support Q contains exactly a
one-dimensional stabilizer subspace. This is checked as
rank(S)-rank(S restricted to the two coordinate copies of Q's complement)=1.
If a local Clifford made the code CSS, any such generator would become pure
X or pure Z: otherwise its two CSS components would give two independent
stabilizers supported in Q. Each qubit sees all three Pauli axes among these
minimal-support generators, and an invertible local Clifford cannot send
three axes into just X and Z. This proves non-LC-CSS for the two finite
instances, including arbitrary changes of stabilizer basis and permutations.
This argument is external to Lean. Recheck from the actual submissions with:

```sh
python supplement/check_binding.py /path/to/challenge/codes/56-24-4.json
python supplement/check_binding.py /path/to/challenge/codes/88-36-4.json
```

The script uses only the Python standard library. It is supplementary evidence,
not the challenge's distance validator. Official validation and deep search
must still be run using the upstream challenge stack.

## Official search receipts

`supplement/deep-ris.json` preserves the four official heuristic outputs,
including their discovered witnesses. Every run used 20,000 Python Pauli RIS
trials, an additional 2,000,000-trial accelerator request on symplectic doubling
(eight threads, pair depth eight), and 50,000 trials per orbit-folded code
under the official fold budget. The fold also tests random Pauli frames;
partition counts are recorded in each output. No wall-clock cap truncated
the main Python or accelerator search. The folding pass has its own official
wall-clock cap. Accelerator output's `trials` is a combined budget label,
not a count of Pauli-scored Python trials. Two fresh seeds per instance
returned lightest-found Pauli weight four. These searches corroborate an
upper bound; they do not prove a lower bound.

The environment was Python 3.12.3 with the challenge lockfile and the official
optional C++ accelerator. The pinned lockfile uses NumPy 2.4.6 and Stim 1.16.0.
The construction was fixed in the supplied handoff before these new seeds.
No `promote.py` search-reuse path is used in the submission packaging.

## Related work and scope

This construction belongs to the known three-check-space XYZ framework of
Baldelli, Orsucci, Lázaro and Battaglioni, *Quantum XYZ Stabilizer Codes*,
[arXiv:2607.14988v1](https://arxiv.org/html/2607.14988v1), Sections III–V.
Equation 67b describes pure-Y logical distance, and Corollary 2 gives a
distance upper bound; neither is itself a rank formula for these instances.
Pairwise overlap cancellation also has close prior in Lee, Okada, Maskara,
Kasai and Zhou, *Design Principles for Ultra-High-Rate Quantum Codes*,
[arXiv:2609.30069v1](https://arxiv.org/html/2609.30069v1), Sections III–IV.
Their framework includes pair partitions and symplectic halving.

Exact-parameter web searches and the current challenge corpus did not locate
an identical published parameter point during preparation. This limited
search does not establish global novelty or inequivalence to all published
codes. The submissions use `novelty: unknown`. No priority, growing-distance,
optimality, all-CSS dominance or experimental resource claim is made.

## Tool disclosure

Model: GPT-6 Astra. Agent environment: OpenAI Codex. AI assistance covered
construction exploration, source and data review, official-tool execution,
literature checking and drafting. Mathematical claims are supported by the
proofs and validation evidence documented above.

## CSS [[663,351,10]] distance proof

`lean663/` contains a standalone Lean 4.35.0 / Std proof for the literal
CSS matrices in [qLDPC Challenge PR #3898](https://github.com/unitaryfoundation/qldpc-challenge/pull/3898).
It proves CSS commutation, exact sector distances 10, and exact binary
phase-free Pauli distance 10 with union support weight. See
[`lean663/README.md`](lean663/README.md) for the construction, replay command
and native-computation trust boundary.
