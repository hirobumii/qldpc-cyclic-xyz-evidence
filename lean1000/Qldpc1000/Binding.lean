import Qldpc1000.Support
import Qldpc1000.Bulk
import Qldpc1000.Structural
import Qldpc1000.Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1100

namespace Qldpc1000

def sumRows : List (List Nat) → Vec n
  | [] => zero
  | r :: rs => add (ofSupport r) (sumRows rs)

theorem sumRows_span (rows rs : List (List Nat))
    (h : ∀ r ∈ rs, r ∈ rows) : RowSpan rows (sumRows rs : Vec n) := by
  induction rs with
  | nil => exact RowSpan.zero
  | cons r rs ih =>
    exact RowSpan.add (RowSpan.row (h _ (by simp)))
      (ih (by intro a ha; exact h a (by simp [ha])))

def rowMap (rows : Fin m → List Nat) : BinaryLinearMap n m :=
  ⟨fun v i => sparseParity (rows i) v,
    by funext i; rw [← dot_ofSupport, dot_zero_right]; rfl,
    by intro u v; funext i; simp only [← dot_ofSupport, dot_add_right, add]⟩

theorem rowMap_zero (rows : List (List Nat)) (mapped : Fin m → List Nat)
    (spans : ∀ i, RowSpan rows (ofSupport (mapped i) : Vec n))
    (v : Vec n) (hv : Kernel rows v) : rowMap mapped v = zero := by
  funext i
  change sparseParity (mapped i) v = false
  rw [← dot_ofSupport]
  exact span_annihilated hv (spans i)

def stored (z : Bool) : List (List Nat) := if z then Data.storedZ else Data.storedX
def fullRows (z : Bool) : Array (List Nat) := if z then Data.fullZ else Data.fullX
def kinds (z : Bool) : Array Nat := if z then Data.kindsZ else Data.kindsX
def kind (z : Bool) (q : Fin 1000) : Fin 4 := Fin.ofNat 4 ((kinds z)[q.val]!)
def blockRows (z : Bool) (b : Fin 3) (r : Fin 101) : List Nat :=
  ((if z then Data.blocksZ else Data.blocksX)[b.val]!)[r.val]!
def recipe (z : Bool) (b : Fin 3) (r : Fin 101) : List (List Nat) :=
  ((if z then Data.recipesZ else Data.recipesX)[b.val]!)[r.val]!
def column (z : Bool) (b : Fin 3) (q : Fin 1000) : Nat :=
  ((if z then Data.columnsZ else Data.columnsX)[b.val]!)[q.val]!

def recipeArray (z : Bool) := if z then Data.recipesZ else Data.recipesX
def blockArray (z : Bool) := if z then Data.blocksZ else Data.blocksX
def colArray (z : Bool) := if z then Data.columnsZ else Data.columnsX

theorem bulk_recipe_members : ∀ z, (recipeArray z).toList.all
    (fun br => br.toList.all (fun rs => rs.all (fun row => decide (row ∈ stored z)))) = true := by decide

theorem recipe_members (z : Bool) (b : Fin 3) (r : Fin 101) :
    (recipe z b r).all (fun row => decide (row ∈ stored z)) = true := by
  have h := all_getD (recipeArray z) _ (bulk_recipe_members z) (by rfl) b.val
  exact all_getD (recipeArray z)[b.val]! _ h (by rfl) r.val

theorem bulk_recipe_values : ∀ z (b : Fin 3),
    ((recipeArray z)[b.val]!.toList.zip (blockArray z)[b.val]!.toList).all
      (fun rr => decide (syndrome supportMask rr.1 = supportMask rr.2)) = true := by decide

theorem recipe_block_sizes : ∀ z (b : Fin 3),
    (recipeArray z)[b.val]!.size = 101 ∧ (blockArray z)[b.val]!.size = 101 := by decide

theorem decode_sumRows (rs : List (List Nat)) :
    decode n (syndrome supportMask rs) = (sumRows rs : Vec n) := by
  induction rs with
  | nil => exact decode_zero n
  | cons r rs ih => simp only [syndrome, decode_xor, decode_supportMask, ih, sumRows]

/-- Every recipe is checked as an exact sparse XOR, then transported to the
actual binary vector space. The marker is thereby a proved derived check. -/
theorem recipe_values (z : Bool) (b : Fin 3) (r : Fin 101) (q : Fin 1000) :
    (sumRows (recipe z b r) : Vec 1000) q = ofSupport (blockRows z b r) q := by
  have h := all_zip_getD (recipeArray z)[b.val]! (blockArray z)[b.val]!
    (fun rs row => decide (syndrome supportMask rs = supportMask row))
    (bulk_recipe_values z b) r.val
    (by rw [(recipe_block_sizes z b).1]; exact r.isLt)
    (by rw [(recipe_block_sizes z b).2]; exact r.isLt)
  have he : syndrome supportMask (recipe z b r) = supportMask (blockRows z b r) := of_decide_eq_true h
  have hv := congrArg (decode 1000) he
  rw [decode_sumRows, decode_supportMask] at hv
  exact congrFun hv q

theorem block_span (z : Bool) (b : Fin 3) (r : Fin 101) :
    RowSpan (stored z) (ofSupport (blockRows z b r) : Vec 1000) := by
  have he : (sumRows (recipe z b r) : Vec 1000) = ofSupport (blockRows z b r) :=
    funext (recipe_values z b r)
  rw [← he]
  apply sumRows_span
  intro row hr
  exact of_decide_eq_true (List.all_eq_true.mp (recipe_members z b r) row hr)

/-- The literal column table is checked against each literal row as a compact
transpose, not by trusting a generated matrix hash. -/
theorem bulk_transpose : ∀ z (b : Fin 3),
    ((blockArray z)[b.val]!.toList.zip (List.range 101)).all
      (fun rr => decide (supportMask rr.1 = bitSlice (colArray z)[b.val]!.toList rr.2)) = true := by decide

theorem sparse_basis (row : List Nat) (q : Fin n) :
    sparseParity row (oneHot q.val : Vec n) = ofSupport row q := by
  rw [← dot_ofSupport, dot_comm, dot_oneHot]
  simp [eval]

theorem block_basis (z : Bool) (b : Fin 3) (q : Fin 1000) (r : Fin 101) :
    sparseParity (blockRows z b r) (oneHot q.val : Vec 1000) =
      (column z b q).testBit r.val := by
  have h := all_zip_getD (blockArray z)[b.val]! (List.range 101).toArray
    (fun row i => decide (supportMask row = bitSlice (colArray z)[b.val]!.toList i))
    (by simpa using bulk_transpose z b) r.val
    (by rw [(recipe_block_sizes z b).2]; exact r.isLt)
    (by simpa using r.isLt)
  have hr : (List.range 101).toArray[r.val]! = r.val := by
    rw [getElem!_pos _ _ (by simpa using r.isLt)]
    simp
  rw [hr] at h
  have he : supportMask (blockRows z b r) = bitSlice (colArray z)[b.val]!.toList r.val := of_decide_eq_true h
  rw [sparse_basis, ← decode_supportMask]
  change (supportMask (blockRows z b r)).testBit q.val = _
  rw [he, testBit_bitSlice, Array.getElem!_toList]
  rfl

theorem bulk_column_bound : ∀ z, (colArray z).toList.all
    (fun a => a.toList.all (fun c => decide (c < 2^101))) = true := by decide

theorem column_bound (z : Bool) (b : Fin 3) (q : Fin 1000) : column z b q < 2^101 := by
  have h := all_getD (colArray z) _ (bulk_column_bound z) (by decide) b.val
  exact of_decide_eq_true (all_getD (colArray z)[b.val]! _ h (by decide) q.val)

theorem kernel_block_zero (z : Bool) (v : Vec 1000) (hv : Kernel (stored z) v) (b : Fin 3) :
    syndrome (column z b) (vecSupport v) = 0 := by
  apply syndrome_zero_of_vector_map_zero (rowMap (blockRows z b)) (column z b)
  · intro q
    funext r
    exact block_basis z b q r
  · exact column_bound z b
  · exact rowMap_zero (stored z) (blockRows z b) (block_span z b) v hv

/- Explicit full/stored kernel relation, with no Gaussian elimination oracle. -/
theorem full_in_blocks : ∀ z (r : Fin 300),
    (fullRows z)[r.val]! = blockRows z (Fin.ofNat 3 (r.val / 100)) (Fin.ofNat 101 (r.val % 100)) := by
  decide

theorem stored_in_full : ∀ z, (stored z).all (fun row => decide (row ∈ (fullRows z).toList)) = true := by
  decide

theorem full_size : ∀ z, (fullRows z).size = 300 := by decide

theorem full_stored_kernel (z : Bool) (v : Vec 1000) :
    Kernel (fullRows z).toList v ↔ Kernel (stored z) v := by
  constructor
  · intro hf row hr
    exact hf row (of_decide_eq_true (List.all_eq_true.mp (stored_in_full z) row hr))
  · intro hs row hr
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hr
    have hib : i < 300 := by simpa [full_size z] using hi
    have hh : (fullRows z)[i]! = row := by
      simpa [getElem!_pos (fullRows z) i (by simpa [full_size z] using hi)] using he
    rw [← hh, full_in_blocks z ⟨i, hib⟩]
    exact span_annihilated hs (block_span z _ _)

end Qldpc1000
