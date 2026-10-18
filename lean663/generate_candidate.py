#!/usr/bin/env python3
"""Deterministically bind immutable candidate.json to Lean literal sparse rows.

No mathematical fact emitted by this generator is trusted by Lean: every claimed
property below is proved by the kernel from definitions in Core.lean.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'data' / 'candidate.json'
TARGET = HERE / 'Qec663Proof' / 'Binding663' / 'Candidate.lean'


def lean_list(xs):
    return '[' + ', '.join(map(str, xs)) + ']'


def generate(data, digest):
    assert data['n'] == 663
    assert data['code_type'] == 'CSS'
    hx, hz = (data['checks'][s] for s in ['X', 'Z'])
    assert len(hx) == len(hz) == 156
    assert all(len(s) == len(set(s)) and all(0 <= i < 663 for i in s)
               for s in hx + hz)
    x, z = (data['distance'][s]['witness'] for s in ['X', 'Z'])
    assert len(x) == len(z) == 10
    shifted = lambda s: sorted((i // 39) * 39 + (i + 1) % 39 for i in s)
    sx, sz = shifted(z), shifted(x)
    parity = lambda u, v: len(set(u) & set(v)) % 2
    assert all(parity(s, x) == 0 for s in hz)
    assert all(parity(s, z) == 0 for s in hx)
    assert all(parity(s, sx) == 0 for s in hx)
    assert all(parity(s, sz) == 0 for s in hz)
    assert parity(x, sx) == parity(z, sz) == 1
    out = [
        'import Qec663Proof.Binding663.Core', '',
        '/-! Literal binding of the actual [[663,351,10]] candidate.',
        f'Immutable JSON SHA256: {digest}',
        'Regenerate or audit with python3 generate_candidate.py [--check].',
        'All proofs use transparent kernel computation; no native_decide. -/', '',
        'set_option maxRecDepth 1000000',
        'set_option maxHeartbeats 0', '',
        'namespace Binding663', '',
        'def n : Nat := 663', '',
    ]
    for name, rows in [('hx', hx), ('hz', hz)]:
        out += [f'def {name} : List (List Nat) := [']
        out += ['  ' + lean_list(r) + (',' if j < len(rows)-1 else '')
                for j, r in enumerate(rows)]
        out += [']', '']
    for name, support in [('xWitnessSupport', x), ('zWitnessSupport', z),
                          ('xSeparatorSupport', sx), ('zSeparatorSupport', sz)]:
        out += [f'def {name} : List Nat := {lean_list(support)}', '']
    for name in ['xWitness', 'zWitness', 'xSeparator', 'zSeparator']:
        out += [f'def {name} : Vec 663 := ofSupport {name}Support', '']
    out += ['''/-- Literal row dimensions and finite-coordinate validity. -/
theorem hx_length : hx.length = 156 := by decide
theorem hz_length : hz.length = 156 := by decide

def rowsWellFormed (rows : List (List Nat)) : Bool :=
  rows.all fun s => decide s.Nodup && s.all (fun i => decide (i < 663))

theorem literal_rows_wellFormed : rowsWellFormed (hx ++ hz) = true := by decide

theorem rowsWellFormed_sound {rows : List (List Nat)}
    (h : rowsWellFormed rows = true) :
    ∀ s ∈ rows, s.Nodup ∧ ∀ i ∈ s, i < 663 := by
  intro s hs
  have hp := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h s hs)
  constructor
  · exact of_decide_eq_true hp.1
  · intro i hi
    exact of_decide_eq_true (List.all_eq_true.mp hp.2 i hi)

theorem actual_rows_are_binary_supports :
    ∀ s ∈ hx ++ hz, s.Nodup ∧ ∀ i ∈ s, i < 663 :=
  rowsWellFormed_sound literal_rows_wellFormed

/-- Both primal witnesses are in the actual opposite-check kernels. -/
theorem x_kernel : Kernel hz xWitness :=
  kernelCheck_sound hz xWitness (by decide)

theorem z_kernel : Kernel hx zWitness :=
  kernelCheck_sound hx zWitness (by decide)

/-- Explicit separating dual functionals vanish on every stabilizer row. -/
theorem x_separator_kernel : Kernel hx xSeparator :=
  kernelCheck_sound hx xSeparator (by decide)

theorem z_separator_kernel : Kernel hz zSeparator :=
  kernelCheck_sound hz zSeparator (by decide)

theorem x_separator_odd : dot xWitness xSeparator = true := by
  rw [xWitness, dot_ofSupport]
  decide

theorem z_separator_odd : dot zWitness zSeparator = true := by
  rw [zWitness, dot_ofSupport]
  decide

/-- True nonmembership in the full linear span, rather than unequal supports. -/
theorem x_not_rowSpan : ¬ RowSpan hx xWitness :=
  not_span_of_separator x_separator_kernel x_separator_odd

theorem z_not_rowSpan : ¬ RowSpan hz zWitness :=
  not_span_of_separator z_separator_kernel z_separator_odd

theorem x_weight : weight xWitness = 10 := by decide
theorem z_weight : weight zWitness = 10 := by decide

theorem x_logical : Logical hz hx xWitness := ⟨x_kernel, x_not_rowSpan⟩
theorem z_logical : Logical hx hz zWitness := ⟨z_kernel, z_not_rowSpan⟩

theorem dX_le10 : DistanceAtMost (n := 663) hz hx 10 :=
  ⟨xWitness, x_logical, by rw [x_weight]; exact Nat.le_refl _⟩

theorem dZ_le10 : DistanceAtMost (n := 663) hx hz 10 :=
  ⟨zWitness, z_logical, by rw [z_weight]; exact Nat.le_refl _⟩

end Binding663''', '']
    return '\n'.join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    raw = SOURCE.read_bytes()
    expected = generate(json.loads(raw), hashlib.sha256(raw).hexdigest())
    if args.check:
        assert TARGET.read_text() == expected, 'literal Lean binding differs from immutable JSON'
        print('PASS: all 312 literal rows and four witness supports match deterministic generation')
    else:
        TARGET.write_text(expected)
        print(TARGET)


if __name__ == '__main__':
    main()
