import Qec663Proof.Binding663.Cyclic
import Qec663Proof.VectorFacts
import Qec663Proof.WeightSingleton

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Qec663.Structure
open Binding663

private theorem xor_interchange (a b c d : Bool) :
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem eval_zero {n : Nat} (i : Nat) : eval (zero : Vec n) i = false := by
  simp [eval, zero]

theorem eval_add {n : Nat} (u v : Vec n) (i : Nat) :
    eval (add u v) i = (eval u i ^^ eval v i) := by
  simp only [eval]
  split <;> simp [add]

theorem sparseParity_zero {n : Nat} (s : List Nat) : sparseParity s (zero : Vec n) = false := by
  induction s with
  | nil => rfl
  | cons i s ih => simp [sparseParity, eval_zero, ih]

theorem sparseParity_add {n : Nat} (s : List Nat) (u v : Vec n) :
    sparseParity s (add u v) = (sparseParity s u ^^ sparseParity s v) := by
  induction s with
  | nil => rfl
  | cons i s ih =>
    simp only [sparseParity, eval_add, ih]
    exact xor_interchange _ _ _ _

def targetLinear (poly : List Nat) (minus : Bool) : BinaryLinearMap 39 39 :=
  ⟨targetMap poly minus, by
      funext r
      exact sparseParity_zero (targetSupport poly minus r),
    by
      intro u v
      funext r
      exact sparseParity_add (targetSupport poly minus r) u v⟩

def syndromeLinear (polys : Fin 4 → List Nat) (minus : Bool) : BinaryLinearMap 156 39 :=
  ⟨syndromeMap polys minus, by
      funext r
      exact sparseParity_zero (syndromeSupport polys minus r),
    by
      intro u v
      funext r
      exact sparseParity_add (syndromeSupport polys minus r) u v⟩

def composeLinear {n m k : Nat} (f : BinaryLinearMap m k) (g : BinaryLinearMap n m) : BinaryLinearMap n k :=
  ⟨fun v => f (g v), by change f (g zero) = zero; rw [g.map_zero,f.map_zero],
    by intro u v; change f (g (add u v)) = _; rw [g.map_add,f.map_add]⟩

def identityLinear {n : Nat} : BinaryLinearMap n n := ⟨id, rfl, by intros; rfl⟩

/-- The actual singleton-column characterization for any literal syndrome map. -/
theorem syndrome_singleton_column
    (polys : Fin 4 → List Nat) (minus : Bool) (v : Vec 156)
    (h : weight v = 1) :
    ∃ p : Fin 156, syndromeMap polys minus v =
      syndromeMap polys minus (oneHot p.val) := by
  obtain ⟨p,hp⟩ := weight_one_basis v h
  exact ⟨p,congrArg (syndromeMap polys minus) hp⟩

#print axioms sparseParity_add
#print axioms syndrome_singleton_column
end Qec663.Structure
