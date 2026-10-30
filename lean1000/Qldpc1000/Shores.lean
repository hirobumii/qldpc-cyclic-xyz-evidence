import Qldpc1000.SmallGraph

namespace Qldpc1000

def restrictMap (p : Fin n → Prop) [DecidablePred p] : BinaryLinearMap n n :=
  ⟨fun v q => if p q then v q else false,
    by funext q; simp [zero],
    by intro u v; funext q; by_cases h : p q <;> simp [h, add]⟩

theorem restrict_basis (p : Fin n → Prop) [DecidablePred p] (u : Fin n) (h : p u) :
    restrictMap p (oneHot u.val) = oneHot u.val := by
  funext q
  by_cases he : q=u
  · subst q; simp [restrictMap, oneHot, h]
  · have hn : q.val ≠ u.val := fun hh => he (Fin.ext hh)
    simp [restrictMap, oneHot, hn]

theorem restrict_basis_zero (p : Fin n → Prop) [DecidablePred p] (u : Fin n) (h : ¬ p u) :
    restrictMap p (oneHot u.val) = zero := by
  funext q
  by_cases he : q=u
  · subst q; simp [restrictMap, oneHot, h, zero]
  · have hn : q.val ≠ u.val := fun hh => he (Fin.ext hh)
    simp [restrictMap, oneHot, hn, zero]

/-- Transport is required only for the actual selected edges, not for every
coordinate of the ambient code. -/
theorem decode_syndrome_on {E : Type} (f : BinaryLinearMap n m) (c d : E → Nat) (s : List E)
    (h : ∀ q∈s, decode m (d q) = f (decode n (c q))) :
    decode m (syndrome d s) = f (decode n (syndrome c s)) := by
  induction s with
  | nil => simp only [syndrome, decode_zero, f.map_zero]
  | cons q qs ih =>
    simp only [syndrome, decode_xor, f.map_add]
    rw [h q (by simp), ih (by intro a ha; exact h a (by simp [ha]))]

/-- A zero edge boundary has zero incidence on each shore separately. -/
theorem shore_syndromes_zero {E : Type} (p : Fin n → Prop) [DecidablePred p]
    (left right : E → Fin n) (c : E → Nat) (s : List E)
    (ends : ∀ q∈s, decode n (c q) = add (oneHot (left q).val) (oneHot (right q).val))
    (left_shore : ∀ q∈s, p (left q)) (right_shore : ∀ q∈s, ¬p (right q))
    (hz : syndrome c s = 0) :
    syndrome (fun q => 2^(left q).val) s = 0 ∧
    syndrome (fun q => 2^(right q).val) s = 0 := by
  constructor
  · apply (decode_zero_iff (syndrome_bounded n (fun q => 2^(left q).val) s
      (fun q _ => Nat.pow_lt_pow_right (by decide) (left q).isLt))).mp
    have h := decode_syndrome_on (restrictMap p) c (fun q => 2^(left q).val) s (by
      intro q hq
      rw [ends q hq, (restrictMap p).map_add, restrict_basis p _ (left_shore q hq),
        restrict_basis_zero p _ (right_shore q hq), decode_pow]
      funext i
      simp [add, zero])
    rw [h, hz, decode_zero, (restrictMap p).map_zero]
  · apply (decode_zero_iff (syndrome_bounded n (fun q => 2^(right q).val) s
      (fun q _ => Nat.pow_lt_pow_right (by decide) (right q).isLt))).mp
    have h := decode_syndrome_on (restrictMap (fun u => ¬p u)) c (fun q => 2^(right q).val) s (by
      intro q hq
      rw [ends q hq, (restrictMap (fun u => ¬p u)).map_add,
        restrict_basis_zero (fun u => ¬p u) _ (by simpa using left_shore q hq),
        restrict_basis (fun u => ¬p u) _ (right_shore q hq), decode_pow]
      funext i
      simp [add, zero])
    rw [h, hz, decode_zero, (restrictMap (fun u => ¬p u)).map_zero]

end Qldpc1000
