import Std

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Qldpc1000.Commutation

/-- The period-four table for2^j mod5. -/
def scale (j : Nat) : Nat := [1,2,4,3][j % 4]!
theorem scale_is_power : ∀ j : Fin 20, scale j.val = (2^j.val)%5 := by decide

def first (u : Fin 100) : Fin 5 := Fin.ofNat 5 u.val
def second (u : Fin 100) : Fin 20 := Fin.ofNat 20 (u.val/5)
def pack (i : Fin 5) (j : Fin 20) : Fin 100 := ⟨i.val+5*j.val, by
  have := i.isLt; have := j.isLt; omega⟩

@[simp] theorem first_pack (i : Fin 5) (j : Fin 20) : first (pack i j) = i := by
  apply Fin.ext
  simp only [first, pack, Fin.val_ofNat]
  have := i.isLt
  omega
@[simp] theorem second_pack (i : Fin 5) (j : Fin 20) : second (pack i j) = j := by
  apply Fin.ext
  simp only [second, pack, Fin.val_ofNat]
  have := i.isLt; have := j.isLt
  omega

def action (j : Fin 20) (i : Fin 5) : Fin 5 := Fin.ofNat 5 (scale j.val*i.val)

/- Only the small scalar-action laws are finite kernel checks. The group
associativity and all left/right commutation are then symbolic consequences. -/
theorem action_add : ∀ j i k, action j (i+k) = action j i + action j k := by decide
theorem action_comp : ∀ j k i, action (j+k) i = action j (action k i) := by decide

theorem fin_add_assoc (i j k : Fin n) : (i+j)+k = i+(j+k) := by
  apply Fin.ext
  simp only [Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

/-- G=C5 semidirect C20, exactly(i,j)(k,l)=(i+2^j*k,j+l), encoded i+5*j. -/
def mul (x y : Fin 100) : Fin 100 :=
  pack (first x + action (second x) (first y)) (second x + second y)

theorem mul_assoc (x y z : Fin 100) : mul (mul x y) z = mul x (mul y z) := by
  simp only [mul, first_pack, second_pack, action_add, action_comp, fin_add_assoc]

/-- Left and right regular multiplication commute in every associative
operation. No enumeration of pairs of code rows enters this identity. -/
theorem left_right_of_assoc {α : Type} (op : α → α → α)
    (assoc : ∀ x y z, op (op x y) z = op x (op y z)) (a b u : α) :
    op (op a u) b = op a (op u b) := assoc a u b

end Qldpc1000.Commutation
