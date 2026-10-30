import Qldpc1000.Binding
import Qldpc1000.Symmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Qldpc1000
open Symmetry

def targetKind (cc : Bool) (b : Fin 3) : Fin 4 := if cc then 3 else b.castSucc
def localColumn (z cc : Bool) (b : Fin 3) (q : Fin 1000) : Nat :=
  if kind z q = targetKind cc b then column z b q % 2^100 else 0
def localNeighbors (z cc : Bool) (b : Fin 3) (r : Nat) : List (Fin 1000) :=
  ((((if z then (if cc then Data.ccNeighborsZ else Data.vvNeighborsZ)
       else (if cc then Data.ccNeighborsX else Data.vvNeighborsX))[b.val]!)[r]!).map (Fin.ofNat 1000))

theorem kind_table : ∀ z,
    ((kinds z).toList.zip (List.range 1000)).all
      (fun ki => decide (Fin.ofNat 4 ki.1 = expectedKind z (Fin.ofNat 1000 ki.2))) = true := by decide

theorem kind_size : ∀ z, (kinds z).size = 1000 := by decide

theorem kind_formula (z : Bool) (q : Fin 1000) : kind z q = expectedKind z q := by
  have h := all_zip_getD (kinds z) (List.range 1000).toArray
    (fun k i => decide (Fin.ofNat 4 k = expectedKind z (Fin.ofNat 1000 i)))
    (by simpa using kind_table z) q.val
    (by rw [kind_size]; exact q.isLt) (by simpa using q.isLt)
  have hi : (List.range 1000).toArray[q.val]! = q.val := by
    rw [getElem!_pos _ _ (by simpa using q.isLt)]; simp
  rw [hi] at h
  have hq : Fin.ofNat 1000 q.val = q := by apply Fin.ext; exact Nat.mod_eq_of_lt q.isLt
  simpa [kind, hq] using of_decide_eq_true h

def neighborArray (z cc : Bool) :=
  if z then (if cc then Data.ccNeighborsZ else Data.vvNeighborsZ)
  else (if cc then Data.ccNeighborsX else Data.vvNeighborsX)

theorem neighbor_sizes : ∀ z cc (b : Fin 3), (neighborArray z cc)[b.val]!.size = 100 := by decide

/-- The100 physical rows are checked sequentially against their sparse local
neighbor lists. The101st derived marker is outside this incidence graph. -/
theorem neighbors_table : ∀ z cc (b : Fin 3),
    ((blockArray z)[b.val]!.toList.zip (neighborArray z cc)[b.val]!.toList).all
      (fun rn => decide ((rn.1.filter
        (fun i => decide (expectedKind z (Fin.ofNat 1000 i) = targetKind cc b))).map
        (Fin.ofNat 1000) = rn.2.map (Fin.ofNat 1000))) = true := by decide

theorem neighbors_formula (z cc : Bool) (b : Fin 3) (r : Fin 100) :
    ((blockRows z b r.castSucc).filter
      (fun i => decide (kind z (Fin.ofNat 1000 i) = targetKind cc b))).map
      (Fin.ofNat 1000) = localNeighbors z cc b r.val := by
  have h := all_zip_getD (blockArray z)[b.val]! (neighborArray z cc)[b.val]!
    (fun row ns => decide ((row.filter
      (fun i => decide (expectedKind z (Fin.ofNat 1000 i) = targetKind cc b))).map
      (Fin.ofNat 1000) = ns.map (Fin.ofNat 1000))) (neighbors_table z cc b) r.val
    (by rw [(recipe_block_sizes z b).2]; have := r.isLt; omega)
    (by rw [neighbor_sizes]; exact r.isLt)
  simp only [kind_formula]
  exact of_decide_eq_true h

theorem local_cover_finite (z cc : Bool) (b : Fin 3) (q : Fin 1000) (r : Fin 100)
    (h : (localColumn z cc b q).testBit r.val = true) : q ∈ localNeighbors z cc b r.val := by
  by_cases good : kind z q = targetKind cc b
  · have hc : (column z b q).testBit r.val = true := by
      rw [localColumn, if_pos good, Nat.testBit_mod_two_pow] at h
      simpa only [r.isLt, decide_true, Bool.true_and] using h
    have hb := block_basis z b q r.castSucc
    rw [sparse_basis] at hb
    have hm := ofSupport_true_mem (blockRows z b r.castSucc) q (hb.trans hc)
    rw [← neighbors_formula z cc b r]
    apply List.mem_map.mpr
    have hq : Fin.ofNat 1000 q.val = q := by apply Fin.ext; exact Nat.mod_eq_of_lt q.isLt
    exact ⟨q.val, List.mem_filter.mpr ⟨hm, by simpa [hq] using good⟩, hq⟩
  · simp [localColumn, good] at h

theorem local_bound (z cc : Bool) (b : Fin 3) (q : Fin 1000) :
    localColumn z cc b q < 2^100 := by
  unfold localColumn
  split
  · exact Nat.mod_lt _ (by decide)
  · decide

theorem local_cover (z cc : Bool) (b : Fin 3) (q : Fin 1000) (r : Nat)
    (h : (localColumn z cc b q).testBit r = true) : q ∈ localNeighbors z cc b r := by
  by_cases hr : r < 100
  · exact local_cover_finite z cc b q ⟨r, hr⟩ h
  · have hp : 2^100 ≤ 2^r := Nat.pow_le_pow_right (by decide) (by omega)
    have hb := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (local_bound z cc b q) hp)
    rw [hb] at h
    contradiction


end Qldpc1000
