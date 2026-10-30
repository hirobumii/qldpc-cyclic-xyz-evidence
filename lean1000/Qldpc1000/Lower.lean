import Qldpc1000.PhaseNonedge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Qldpc1000

theorem syndrome_low (c : α → Nat) (s : List α) :
    syndrome (fun q => c q % 2^100) s = syndrome c s % 2^100 := by
  induction s with
  | nil => rfl
  | cons q qs ih => simp only [syndrome, ih, Nat.xor_mod_two_pow]

def designated (z : Bool) : Fin 3 := if z then 2 else 1

def markerP (b : Fin 3) (k c : Nat) : Bool :=
  decide (Fin.ofNat 4 k = b.castSucc ∨ Fin.ofNat 4 k = 3 → c.testBit 100 = true)
def outsideP (b : Fin 3) (k c : Nat) : Bool :=
  decide (Fin.ofNat 4 k ≠ b.castSucc → Fin.ofNat 4 k ≠ 3 → c = 0)

theorem bulk_marker_outside : ∀ z (b : Fin 3),
    ((kinds z).toList.zip (colArray z)[b.val]!.toList).all
      (fun kc => markerP b kc.1 kc.2 && outsideP b kc.1 kc.2) = true := by decide

theorem kinds_columns_size : ∀ z (b : Fin 3),
    (kinds z).size = 1000 ∧ (colArray z)[b.val]!.size = 1000 := by decide

theorem marker_outside_at (z : Bool) (b : Fin 3) (q : Fin 1000) :
    markerP b (kinds z)[q.val]! (column z b q) = true ∧
    outsideP b (kinds z)[q.val]! (column z b q) = true := by
  apply Bool.and_eq_true_iff.mp
  exact all_zip_getD (kinds z) (colArray z)[b.val]!
    (fun k c => markerP b k c && outsideP b k c)
    (bulk_marker_outside z b) q.val
    (by rw [(kinds_columns_size z b).1]; exact q.isLt)
    (by rw [(kinds_columns_size z b).2]; exact q.isLt)

theorem marker_checked (z : Bool) (b : Fin 3) (q : Fin 1000) :
    kind z q = b.castSucc ∨ kind z q = 3 → (column z b q).testBit 100 = true :=
  of_decide_eq_true (marker_outside_at z b q).1
theorem outside_checked (z : Bool) (b : Fin 3) (q : Fin 1000) :
    kind z q ≠ b.castSucc → kind z q ≠ 3 → column z b q = 0 :=
  of_decide_eq_true (marker_outside_at z b q).2
theorem local_exclusion (z cc : Bool) (b : Fin 3) (s : List (Fin 1000))
    (nd : s.Nodup) (ne : s ≠ []) (small : s.length ≤ 5)
    (good : ∀ q ∈ s, kind z q = targetKind cc b) : syndrome (column z b) s ≠ 0 := by
  intro hz
  have hp := syndrome_bit_parity (column z b) s 100 (by
    intro q hq
    apply marker_checked z b q
    cases cc
    · exact Or.inl (good q hq)
    · exact Or.inr (good q hq))
  have even : s.length % 2 = 0 := by
    rw [hz] at hp
    simpa using hp.symm
  have hn := AlgebraicLocal.no_small z cc b s nd ne small even good
  apply hn
  have hc : syndrome (LocalFormula.formulaColumn z cc b) s =
      syndrome (fun q => column z b q % 2^100) s := by
    apply syndrome_congr
    intro q hq
    rw [← LocalFormula.column_formula]
    simp [localColumn, good q hq]
  rw [hc, syndrome_low, hz]


/-- X:block1 has CC phase±3 against VV±1,±7; Z:block2 has
CC phase±7 against VV±1,±3. Only24 signed-generator arithmetic cases. -/
theorem designated_phase_separation : ∀ z (i : Fin 6) (positive : Bool),
    Commutation.second (Cayley.signed z i) ≠
      Commutation.second (Cayley.signed (!z) (AlgebraicLocal.mkSign (designated z) positive)) := by decide

theorem nonedge_checked (z : Bool) (q u : Fin 1000)
    (hq : kind z q = (designated z).castSucc) (hu : kind z u = 3) :
    column z (designated z) q ≠ column z (designated z) u := by
  intro he
  apply AlgebraicLocal.formula_nonedge z (designated z) (designated_phase_separation z) q u
    (by rw [← kind_formula]; exact hq) (by rw [← kind_formula]; exact hu)
  rw [← LocalFormula.column_formula, ← LocalFormula.column_formula]
  simp only [localColumn, targetKind, Bool.false_eq_true, ↓reduceIte, hq, hu]
  rw [he]

theorem literal_kernel_minimum (z : Bool) (v : Vec 1000)
    (nonzero : v ≠ zero) (kernel : Kernel (stored z) v) : 6 ≤ weight v := by
  apply structural_lower (kind z) (column z)
    (fun b s nd ne small good => local_exclusion z false b s nd ne small good)
    (fun b s nd ne small good => local_exclusion z true b s nd ne small good)
    (marker_checked z) (designated z) (nonedge_checked z) (outside_checked z)
    (vecSupport v) (vecSupport_nodup v) (vecSupport_ne_nil v nonzero)
  exact kernel_block_zero z v kernel

end Qldpc1000
