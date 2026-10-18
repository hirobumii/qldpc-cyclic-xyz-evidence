import Qec663Proof.Binding663.Core

namespace Binding663

theorem weight_zero_iff (v : Vec n) : weight v = 0 ↔ v = zero := by
  constructor
  · intro h
    have he : ((List.finRange n).filter fun i => v i) = [] :=
      List.eq_nil_of_length_eq_zero h
    funext i
    have hm : i ∈ List.finRange n := by simp [List.finRange]
    have hn := List.filter_eq_nil_iff.mp he i hm
    cases hi : v i with
    | false => rfl
    | true => exact False.elim (hn hi)
  · intro h
    subst v
    simp [weight, zero]

/-- Extend a binary vector with a leading zero coordinate. -/
def liftZero (v : Vec n) : Vec (n+1) := Fin.cases false v

@[simp] theorem liftZero_zero : liftZero (zero : Vec n) = zero := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem liftZero_add (u v : Vec n) :
    liftZero (add u v) = add (liftZero u) (liftZero v) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem liftZero_oneHot (i : Fin n) :
    liftZero (oneHot i.val) = oneHot (n := n+1) (i.val+1) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [liftZero, oneHot]
  · simp [liftZero, oneHot]

theorem vector_head_tail (v : Vec (n+1)) :
    v = add (if v 0 then oneHot 0 else zero)
      (liftZero (fun i => v i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · cases h : v 0 <;> simp [h, add, zero, oneHot, liftZero]
  · cases h : v 0 <;> simp [h, add, zero, oneHot, liftZero]

/-- A finite binary linear map, with its actual additive laws. -/
structure BinaryLinearMap (n m : Nat) where
  toFun : Vec n → Vec m
  map_zero : toFun zero = zero
  map_add : ∀ u v, toFun (add u v) = add (toFun u) (toFun v)

instance : CoeFun (BinaryLinearMap n m) (fun _ => Vec n → Vec m) :=
  ⟨BinaryLinearMap.toFun⟩

/-- Finite basis checking suffices for equality on every binary vector.
The basis computations themselves must still be checked for each concrete map. -/
theorem linear_maps_equal_on_vectors (f g : BinaryLinearMap n m)
    (basis : ∀ i : Fin n, f (oneHot i.val) = g (oneHot i.val)) :
    ∀ v, f v = g v := by
  induction n with
  | zero =>
    intro v
    have hv : v = zero := by funext i; exact Fin.elim0 i
    rw [hv, f.map_zero, g.map_zero]
  | succ n ih =>
    let f' : BinaryLinearMap n m :=
      ⟨fun v => f (liftZero v), by change f (liftZero zero) = zero; rw [liftZero_zero, f.map_zero],
        by intro u v; change f (liftZero (add u v)) = _; rw [liftZero_add, f.map_add]⟩
    let g' : BinaryLinearMap n m :=
      ⟨fun v => g (liftZero v), by change g (liftZero zero) = zero; rw [liftZero_zero, g.map_zero],
        by intro u v; change g (liftZero (add u v)) = _; rw [liftZero_add, g.map_add]⟩
    have hb : ∀ i : Fin n, f' (oneHot i.val) = g' (oneHot i.val) := by
      intro i
      change f (liftZero (oneHot i.val)) = g (liftZero (oneHot i.val))
      simp only [liftZero_oneHot]
      exact basis i.succ
    have ht := ih f' g' hb
    intro v
    have htail : f (liftZero (fun i => v i.succ)) =
        g (liftZero (fun i => v i.succ)) := ht _
    have hhead : f (if v 0 then oneHot 0 else zero) =
        g (if v 0 then oneHot 0 else zero) := by
      cases h : v 0 with
      | false => simp [h, f.map_zero, g.map_zero]
      | true => simpa [h] using basis 0
    calc
      f v = f (add (if v 0 then oneHot 0 else zero)
          (liftZero (fun i => v i.succ))) := congrArg f (vector_head_tail v)
      _ = add (f (if v 0 then oneHot 0 else zero))
          (f (liftZero (fun i => v i.succ))) := f.map_add _ _
      _ = add (g (if v 0 then oneHot 0 else zero))
          (g (liftZero (fun i => v i.succ))) := by rw [hhead, htail]
      _ = g (add (if v 0 then oneHot 0 else zero)
          (liftZero (fun i => v i.succ))) := (g.map_add _ _).symm
      _ = g v := congrArg g (vector_head_tail v).symm

#print axioms weight_zero_iff
#print axioms linear_maps_equal_on_vectors

/-- Leading-coordinate decomposition of the actual support count. -/
theorem weight_head_tail (v : Vec (n+1)) :
    weight v = (if v 0 then 1 else 0) + weight (fun i => v i.succ) := by
  cases h : v 0 <;>
    simp [weight, List.finRange_succ, List.filter_map, Function.comp_def, h, Nat.add_comm]

def parity (v : Vec n) : Bool := dot (fun _ => true) v

theorem parity_zero : parity (zero : Vec n) = false := dot_zero_right _

theorem parity_add (u v : Vec n) : parity (add u v) = (parity u ^^ parity v) :=
  dot_add_right _ _ _

/-- The linear XOR augmentation equals Hamming-weight parity. -/
theorem parity_toNat (v : Vec n) : (parity v).toNat = weight v % 2 := by
  induction n with
  | zero => simp [parity, dot, weight, List.finRange_zero]
  | succ n ih =>
    rw [weight_head_tail]
    have hh : parity v = (v 0 ^^ parity (fun i => v i.succ)) := by
      simp [parity, dot]
    rw [hh]
    have ht := ih (fun i => v i.succ)
    cases ha : v 0 <;> cases hb : parity (fun i => v i.succ) <;>
      simp_all <;> omega

#print axioms parity_toNat

/-- XOR augmentation as an honest one-coordinate binary linear map. -/
def parityLinear (n : Nat) : BinaryLinearMap n 1 :=
  ⟨fun v _ => parity v,
   by funext i; exact parity_zero,
   by intro u v; funext i; exact parity_add u v⟩

/-- Basis identities prove Hamming parity preservation on all vectors. -/
theorem weight_parity_of_basis (f : BinaryLinearMap n m)
    (basis : ∀ i : Fin n, parity (f (oneHot i.val)) = parity (oneHot i.val : Vec n))
    (v : Vec n) : weight (f v) % 2 = weight v % 2 := by
  let lhs : BinaryLinearMap n 1 :=
    ⟨fun v => parityLinear m (f v),
      by change parityLinear m (f zero) = zero; rw [f.map_zero, (parityLinear m).map_zero],
      by intro u v; change parityLinear m (f (add u v)) = _
         rw [f.map_add, (parityLinear m).map_add]⟩
  have hb : ∀ i : Fin n, lhs (oneHot i.val) = parityLinear n (oneHot i.val) := by
    intro i
    funext j
    exact basis i
  have he := linear_maps_equal_on_vectors lhs (parityLinear n) hb v
  have hp : parity (f v) = parity v := congrFun he 0
  rw [← parity_toNat, ← parity_toNat, hp]

#print axioms weight_parity_of_basis

end Binding663
