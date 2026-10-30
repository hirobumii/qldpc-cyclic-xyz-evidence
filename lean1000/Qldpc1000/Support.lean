import Qldpc1000.MaskBridge
namespace Qldpc1000
/-- Actual occupied coordinates, in their original finite order. -/
def vecSupport (v : Vec n) : List (Fin n) := (List.finRange n).filter v

theorem vecSupport_sublist (v : Vec n) : (vecSupport v).Sublist (List.finRange n) :=
  List.filter_sublist

theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij he
  have hv := congrArg Fin.val he
  simp [List.finRange] at hv
  omega

theorem vecSupport_nodup (v : Vec n) : (vecSupport v).Nodup :=
  (vecSupport_sublist v).nodup (finRange_nodup n)

theorem vecSupport_length (v : Vec n) : (vecSupport v).length = weight v := rfl

/-- For a nodup finite support, F2 encoding is its characteristic vector. -/
theorem ofFinSupport_apply_of_nodup (s : List (Fin n)) (h : s.Nodup) (q : Fin n) :
    ofFinSupport s q = decide (q ∈ s) := by
  induction s with
  | nil => simp [ofFinSupport, ofSupport, zero]
  | cons a xs ih =>
    have hhead := (List.nodup_cons.mp h).1
    have htail := (List.nodup_cons.mp h).2
    change (decide (q.val = a.val) ^^ ofFinSupport xs q) = decide (q ∈ a :: xs)
    rw [ih htail]
    by_cases he : q = a
    · subst q
      simp [hhead]
    · have hv : q.val ≠ a.val := fun hh => he (Fin.ext hh)
      simp [hv, he]

theorem ofFinSupport_vecSupport (v : Vec n) : ofFinSupport (vecSupport v) = v := by
  funext q
  rw [ofFinSupport_apply_of_nodup _ (vecSupport_nodup v)]
  cases hq : v q <;> simp [vecSupport, List.finRange, hq]

theorem vecSupport_ne_nil (v : Vec n) (h : v ≠ zero) : vecSupport v ≠ [] := by
  intro he
  have hv := ofFinSupport_vecSupport v
  rw [he] at hv
  exact h hv.symm

/-- The physical zero-syndrome vector supplies a zero XOR-mask support without
any assumption about the particular sparse matrix construction. -/
theorem syndrome_zero_of_vector_map_zero (f : BinaryLinearMap n m)
    (column : Fin n → Nat)
    (basis : ∀ q, f (oneHot q.val) = decode m (column q))
    (bounded : ∀ q, column q < 2^m)
    (v : Vec n) (hz : f v = zero) :
    syndrome column (vecSupport v) = 0 := by
  apply syndrome_zero_of_map_zero f column basis bounded
  rw [ofFinSupport_vecSupport]
  exact hz


end Qldpc1000
