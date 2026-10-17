# Pinned Lean toolchain

- Lean: 4.19.0 (release), Linux x86_64.
- Official release: https://github.com/leanprover/lean4/releases/tag/v4.19.0
- Archive: https://github.com/leanprover/lean4/releases/download/v4.19.0/lean-4.19.0-linux.tar.zst
- Downloaded archive SHA-256: `6fe3ce97a58f44e2b3567d455b994eacec5bfe9ae7774f2a573444480ba813fe`.
- Archive bytes: 343842845.
- Dependencies: Core/Std as bundled with that release, no Mathlib or external Lake package.

The SHA-256 is a reproducibility pin measured on the official release download,
not a separately published vendor signature. `scripts/bootstrap_lean.sh` installs
only this pinned official release into the project-local `.toolchain` directory.
It does not change the system PATH or install into the user's home. After setup:

```sh
source env.sh
lake build
```

The proof generators are untrusted transcription aids. Their produced Lean
statements must compile, and all final theorem dependencies must pass
`#print axioms`. No external program's returned truth value is imported as an
axiom. The finite checks use kernel-reduced `decide`, not `native_decide`.

## Build memory

The largest finite certificate modules disable asynchronous elaboration with
`set_option Elab.async false`, and split checks across theorems. This affects
scheduling only; it does not change kernel checking. Do not compile several
copies of the full proof at once on a memory-constrained machine.

## Input boundary

The original JSON files are preserved under `data/`. Their SHA-256 hashes are
in `data/manifest.json`. The Lean kernel checks that the explicit support-list
literals map to the explicit bit-vector candidates; it does not parse JSON or
prove the external SHA-256 implementation correct. `Binding.lean` also proves
that source indices are in range and source lists have no duplicates. An
independent audit should compare the original JSON with the literal data.

The large commutation and distance certificate sets are additionally split into
import-chained modules, each checked by a separate Lean process. This releases
per-process reduction caches and provides restartable `.olean` checkpoints.
