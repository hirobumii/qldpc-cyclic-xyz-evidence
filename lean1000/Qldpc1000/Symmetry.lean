import Qldpc1000.CommutationGroup

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Qldpc1000
namespace Symmetry
open Commutation

def inverse (u : Fin 100) : Fin 100 :=
  pack (Fin.ofNat 5 (5 - (scale (20 - (second u).val) * (first u).val) % 5))
    (Fin.ofNat 20 (20 - (second u).val))

theorem unit_left : ∀ u, mul 0 u = u := by decide
theorem unit_right : ∀ u, mul u 0 = u := by decide
theorem inverse_left : ∀ u, mul (inverse u) u = 0 := by decide
theorem inverse_right : ∀ u, mul u (inverse u) = 0 := by decide

/-- left=true denotes left regular translation; false denotes right. -/
def shift (left : Bool) (g u : Fin 100) : Fin 100 :=
  if left then mul g u else mul u g

theorem shift_inverse (left : Bool) (g u : Fin 100) :
    shift left (inverse g) (shift left g u) = u := by
  cases left
  · simp only [shift, Bool.false_eq_true, ↓reduceIte, mul_assoc, inverse_right, unit_right]
  · simp only [shift, ↓reduceIte, ← mul_assoc, inverse_left, unit_left]

theorem shift_inverse' (left : Bool) (g u : Fin 100) :
    shift left g (shift left (inverse g) u) = u := by
  cases left
  · simp only [shift, Bool.false_eq_true, ↓reduceIte, mul_assoc, inverse_left, unit_right]
  · simp only [shift, ↓reduceIte, ← mul_assoc, inverse_right, unit_left]

theorem shift_self (left : Bool) (u : Fin 100) : shift left (inverse u) u = 0 := by
  cases left <;> simp [shift, inverse_left, inverse_right]

def label (q : Fin 1000) : Fin 10 := ⟨q.val / 100, by have := q.isLt; omega⟩
def vertex (q : Fin 1000) : Fin 100 := ⟨q.val % 100, Nat.mod_lt _ (by decide)⟩
def put (l : Fin 10) (u : Fin 100) : Fin 1000 :=
  ⟨100*l.val+u.val, by have := l.isLt; have := u.isLt; omega⟩

@[simp] theorem label_put (l : Fin 10) (u : Fin 100) : label (put l u) = l := by
  apply Fin.ext
  simp only [label, put]
  have := u.isLt
  omega
@[simp] theorem vertex_put (l : Fin 10) (u : Fin 100) : vertex (put l u) = u := by
  apply Fin.ext
  simp only [vertex, put]
  have := u.isLt
  omega
@[simp] theorem put_parts (q : Fin 1000) : put (label q) (vertex q) = q := by
  apply Fin.ext
  simp only [put, label, vertex]
  omega

def moveEdge (left : Bool) (g : Fin 100) (q : Fin 1000) : Fin 1000 :=
  put (label q) (shift left g (vertex q))

@[simp] theorem move_label (left : Bool) (g : Fin 100) (q : Fin 1000) :
    label (moveEdge left g q) = label q := label_put _ _
@[simp] theorem move_vertex (left : Bool) (g : Fin 100) (q : Fin 1000) :
    vertex (moveEdge left g q) = shift left g (vertex q) := vertex_put _ _

theorem move_inverse (left : Bool) (g : Fin 100) (q : Fin 1000) :
    moveEdge left (inverse g) (moveEdge left g q) = q := by
  simp only [moveEdge, label_put, vertex_put, shift_inverse, put_parts]

theorem move_injective (left : Bool) (g : Fin 100) (q r : Fin 1000)
    (h : moveEdge left g q = moveEdge left g r) : q = r := by
  have he := congrArg (moveEdge left (inverse g)) h
  simpa only [move_inverse] using he

theorem normalize (left : Bool) (q : Fin 1000) :
    moveEdge left (inverse (vertex q)) q = put (label q) 0 := by
  simp only [moveEdge, shift_self]

def expectedKind (z : Bool) (q : Fin 1000) : Fin 4 :=
  if (label q).val < 9 then
    if z then Fin.ofNat 4 ((label q).val / 3) else Fin.ofNat 4 ((label q).val % 3)
  else 3

end Symmetry
end Qldpc1000
