import Qldpc1000.LocalGraph
import Qldpc1000.CommutationConcrete
import Qldpc1000.Symmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1100
namespace Qldpc1000
namespace LocalFormula
open Commutation Symmetry

def edgeStep (z cc : Bool) (block : Fin 3) (l : Fin 10) (u : Fin 100) : Fin 100 :=
  if cc then if z then left block u else rightInv block u
  else if z then right (Fin.ofNat 3 (l.val % 3)) u
  else leftInv (Fin.ofNat 3 (l.val / 3)) u

def formulaColumn (z cc : Bool) (b : Fin 3) (q : Fin 1000) : Nat :=
  if expectedKind z q = targetKind cc b then
    (2^(vertex q).val) ^^^ (2^(edgeStep z cc b (label q) (vertex q)).val)
  else 0

def formulaNeighbors (z cc : Bool) (b : Fin 3) (r : Nat) : List (Fin 1000) :=
  if r < 100 then
    ((if z then zRow leftInv rightInv b (Fin.ofNat 100 r)
      else xRow left right b (Fin.ofNat 100 r)).filter
        (fun i => decide (expectedKind z (Fin.ofNat 1000 i) = targetKind cc b))).map
      (Fin.ofNat 1000)
  else []

/-- The low100 coefficients of every published block column match its two
explicit group-graph endpoints. Checking uses a sequential table traversal. -/
theorem column_table : ∀ z cc (b : Fin 3),
    ((colArray z)[b.val]!.toList.zip (List.range 1000)).all (fun ci =>
      decide ((if expectedKind z (Fin.ofNat 1000 ci.2) = targetKind cc b then ci.1 % 2^100 else 0)
        = formulaColumn z cc b (Fin.ofNat 1000 ci.2))) = true := by decide

theorem col_size : ∀ z (b : Fin 3), (colArray z)[b.val]!.size = 1000 := by decide

theorem column_formula (z cc : Bool) (b : Fin 3) (q : Fin 1000) :
    localColumn z cc b q = formulaColumn z cc b q := by
  have h := all_zip_getD (colArray z)[b.val]! (List.range 1000).toArray
    (fun c i => decide ((if expectedKind z (Fin.ofNat 1000 i) = targetKind cc b then c % 2^100 else 0)
      = formulaColumn z cc b (Fin.ofNat 1000 i)))
    (by simpa using column_table z cc b) q.val
    (by rw [col_size]; exact q.isLt) (by simpa using q.isLt)
  have hi : (List.range 1000).toArray[q.val]! = q.val := by
    rw [getElem!_pos _ _ (by simpa using q.isLt)]; simp
  rw [hi] at h
  have hq : Fin.ofNat 1000 q.val = q := by apply Fin.ext; exact Nat.mod_eq_of_lt q.isLt
  simpa [localColumn, kind_formula, hq, column, colArray] using of_decide_eq_true h

/-- Only short neighbor lists are bound to the fast formula checker. -/
theorem neighbors_perm : ∀ z cc b (r : Fin 100),
    (formulaNeighbors z cc b r.val).Perm (localNeighbors z cc b r.val) := by decide

theorem formula_bound (z cc : Bool) (b : Fin 3) (q : Fin 1000) :
    formulaColumn z cc b q < 2^100 := by rw [← column_formula]; exact local_bound z cc b q

theorem formula_cover (z cc : Bool) (b : Fin 3) (q : Fin 1000) (r : Nat)
    (h : (formulaColumn z cc b q).testBit r = true) : q ∈ formulaNeighbors z cc b r := by
  by_cases hr : r < 100
  · have hc : (localColumn z cc b q).testBit r = true := by rwa [column_formula]
    exact (neighbors_perm z cc b ⟨r, hr⟩).mem_iff.mpr (local_cover z cc b q r hc)
  · have hp : 2^100 ≤ 2^r := Nat.pow_le_pow_right (by decide) (by omega)
    have hz := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (formula_bound z cc b q) hp)
    rw [hz] at h
    contradiction

end LocalFormula
end Qldpc1000
