import Qec663Proof.Binding663.Cyclic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Binding663

theorem sparseParity_append (s t : List Nat) (v : Vec n) :
    sparseParity (s ++ t) v = (sparseParity s v ^^ sparseParity t v) := by
  induction s with
  | nil => simp [sparseParity]
  | cons i is ih => simp only [List.cons_append, sparseParity, ih, Bool.xor_assoc]

theorem sparseParity_perm {s t : List Nat} (h : s.Perm t) (v : Vec n) :
    sparseParity s v = sparseParity t v := by
  induction h with
  | nil => rfl
  | cons i h ih => simp only [sparseParity, ih]
  | swap i j is =>
      simp only [sparseParity]
      cases eval v i <;> cases eval v j <;> cases sparseParity is v <;> rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Push a sparse row along a genuine map of finite coordinate spaces.
The sentinel n preserves the zero extension on out-of-range local entries. -/
def pushSupport (ι : Fin m → Fin n) (s : List Nat) : List Nat :=
  s.map fun j => if h : j < m then (ι ⟨j, h⟩).val else n

theorem sparseParity_pushSupport (ι : Fin m → Fin n) (s : List Nat) (v : Vec n) :
    sparseParity (pushSupport ι s) v = sparseParity s (fun j => v (ι j)) := by
  induction s with
  | nil => rfl
  | cons j js ih =>
      change (eval v (if h : j < m then (ι ⟨j, h⟩).val else n) ^^
        sparseParity (pushSupport ι js) v) =
        (eval (fun j => v (ι j)) j ^^ sparseParity js (fun j => v (ι j)))
      rw [ih]
      congr 1
      by_cases hj : j < m
      · simp [eval, hj, (ι ⟨j, hj⟩).isLt]
      · simp [eval, hj]

def xPhysicalRow (i : Fin 4) (r : Fin 39) : List Nat :=
  pushSupport (xSliceIndex i) (syndromeSupport bSupports true r) ++
    pushSupport ccIndex (targetSupport (aSupports i) true r)

def zPhysicalRow (i : Fin 4) (r : Fin 39) : List Nat :=
  pushSupport (zSliceIndex i) (syndromeSupport aSupports false r) ++
    pushSupport ccIndex (targetSupport (bSupports i) false r)

/-- Exact literal matrix binding, including the displayed row order. -/
theorem literal_hz_rows : ∀ (i : Fin 4) (r : Fin 39),
    (hz.get ⟨i.val * 39 + r.val, by rw [hz_length]; omega⟩).Perm
      (xPhysicalRow i r) := by decide

theorem literal_hx_rows : ∀ (i : Fin 4) (r : Fin 39),
    (hx.get ⟨i.val * 39 + r.val, by rw [hx_length]; omega⟩).Perm
      (zPhysicalRow i r) := by decide

theorem x_kernel_slice_equation (v : Vec 663) (h : Kernel hz v) (i : Fin 4) :
    xSyndrome (xSlice v i) = xTarget i (ccPart v) := by
  funext r
  have hr := h _ (List.get_mem hz ⟨i.val * 39 + r.val, by rw [hz_length]; omega⟩)
  rw [dot_ofSupport] at hr
  rw [sparseParity_perm (literal_hz_rows i r), xPhysicalRow,
    sparseParity_append, sparseParity_pushSupport, sparseParity_pushSupport] at hr
  change (xSyndrome (xSlice v i) r ^^ xTarget i (ccPart v) r) = false at hr
  cases hs : xSyndrome (xSlice v i) r <;>
    cases ht : xTarget i (ccPart v) r <;> simp_all

theorem z_kernel_slice_equation (v : Vec 663) (h : Kernel hx v) (i : Fin 4) :
    zSyndrome (zSlice v i) = zTarget i (ccPart v) := by
  funext r
  have hr := h _ (List.get_mem hx ⟨i.val * 39 + r.val, by rw [hx_length]; omega⟩)
  rw [dot_ofSupport] at hr
  rw [sparseParity_perm (literal_hx_rows i r), zPhysicalRow,
    sparseParity_append, sparseParity_pushSupport, sparseParity_pushSupport] at hr
  change (zSyndrome (zSlice v i) r ^^ zTarget i (ccPart v) r) = false at hr
  cases hs : zSyndrome (zSlice v i) r <;>
    cases ht : zTarget i (ccPart v) r <;> simp_all

def xCoordinatePartition : List (Fin 663) :=
  (List.finRange 39).map ccIndex ++
  (List.finRange 156).map (xSliceIndex 0) ++
  (List.finRange 156).map (xSliceIndex 1) ++
  (List.finRange 156).map (xSliceIndex 2) ++
  (List.finRange 156).map (xSliceIndex 3)

def zCoordinatePartition : List (Fin 663) :=
  (List.finRange 39).map ccIndex ++
  (List.finRange 156).map (zSliceIndex 0) ++
  (List.finRange 156).map (zSliceIndex 1) ++
  (List.finRange 156).map (zSliceIndex 2) ++
  (List.finRange 156).map (zSliceIndex 3)

theorem x_partition_perm :
    (List.finRange 663).Perm xCoordinatePartition := by decide

theorem z_partition_perm :
    (List.finRange 663).Perm zCoordinatePartition := by decide

theorem x_weight_partition (v : Vec 663) :
    weight v = weight (ccPart v) + weight (xSlice v 0) + weight (xSlice v 1) +
      weight (xSlice v 2) + weight (xSlice v 3) := by
  have hw := x_partition_perm.countP_eq v
  simp only [xCoordinatePartition, List.countP_append, List.countP_map] at hw
  simpa only [weight, ← List.countP_eq_length_filter, ccPart, xSlice, Function.comp_def] using hw

theorem z_weight_partition (v : Vec 663) :
    weight v = weight (ccPart v) + weight (zSlice v 0) + weight (zSlice v 1) +
      weight (zSlice v 2) + weight (zSlice v 3) := by
  have hw := z_partition_perm.countP_eq v
  simp only [zCoordinatePartition, List.countP_append, List.countP_map] at hw
  simpa only [weight, ← List.countP_eq_length_filter, ccPart, zSlice, Function.comp_def] using hw

end Binding663
