import Qldpc1000.CommutationAlgebra
import Qldpc1000.CommutationGroup
import Qldpc1000.Binding

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Qldpc1000.Commutation

def a (k : Fin 3) : Fin 100 := if k = 0 then 5 else if k = 1 then 6 else 36
def ai (k : Fin 3) : Fin 100 := if k = 0 then 95 else if k = 1 then 97 else 68
def b (j : Fin 3) : Fin 100 := if j = 0 then 5 else if j = 1 then 16 else 19
def bi (j : Fin 3) : Fin 100 := if j = 0 then 95 else if j = 1 then 88 else 87
def left (k : Fin 3) (u : Fin 100) : Fin 100 := mul (a k) u
def leftInv (k : Fin 3) (u : Fin 100) : Fin 100 := mul (ai k) u
def right (j : Fin 3) (u : Fin 100) : Fin 100 := mul u (b j)
def rightInv (j : Fin 3) (u : Fin 100) : Fin 100 := mul u (bi j)

/- These small action tables establish the concrete premises of the generic
algebraic theorem. They use kernel reduction, never native evaluation. -/
theorem left_inverse : ∀ k u, left k (leftInv k u) = u := by decide
theorem inverse_left : ∀ k u, leftInv k (left k u) = u := by decide
theorem right_inverse : ∀ j u, right j (rightInv j u) = u := by decide
theorem inverse_right : ∀ j u, rightInv j (right j u) = u := by decide
theorem actions_commute (k j : Fin 3) (u : Fin 100) :
    right j (left k u) = left k (right j u) :=
  left_right_of_assoc mul mul_assoc (a k) (b j) u

theorem formula_commutes (j k : Fin 3) (t s : Fin 100) :
    dot (ofSupport (xRow left right j t) : Vec 1000)
      (ofSupport (zRow leftInv rightInv k s)) = false :=
  product_rows_commute left right leftInv rightInv
    left_inverse inverse_left right_inverse inverse_right actions_commute j k t s

/-- The independent original rows are0..98 in each original100-row block. -/
def rowBlock (i : Fin 297) : Fin 3 := Fin.ofNat 3 (i.val / 99)
def rowVertex (i : Fin 297) : Fin 100 := Fin.ofNat 100 (i.val % 99)
def formulaRow (z : Bool) (i : Fin 297) : List Nat :=
  if z then zRow leftInv rightInv (rowBlock i) (rowVertex i)
  else xRow left right (rowBlock i) (rowVertex i)

/-- Artifact/formula binding is separate from product commutation. This only
checks that594 literal lists of length8 permute the construction formulas. -/
theorem stored_formula : ∀ z (i : Fin 297),
    ((stored z)[i.val]!).Perm (formulaRow z i) := by decide
theorem stored_length : ∀ z, (stored z).length = 297 := by decide

theorem stored_vector_formula (z : Bool) (i : Fin 297) :
    (ofSupport ((stored z)[i.val]!) : Vec 1000) = ofSupport (formulaRow z i) := by
  exact ofSupport_perm (stored_formula z i)

theorem literal_css_commutes : ∀ xr ∈ stored false, ∀ zr ∈ stored true,
    dot (ofSupport xr : Vec 1000) (ofSupport zr) = false := by
  intro xr hx zr hz
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, hf⟩ := List.mem_iff_getElem.mp hz
  have hib : i < 297 := by simpa [stored_length] using hi
  have hjb : j < 297 := by simpa [stored_length] using hj
  have hx' : (stored false)[i]! = xr := by simpa [getElem!_pos (stored false) i hi] using he
  have hz' : (stored true)[j]! = zr := by simpa [getElem!_pos (stored true) j hj] using hf
  rw [← hx', ← hz', stored_vector_formula false ⟨i, hib⟩,
    stored_vector_formula true ⟨j, hjb⟩]
  exact formula_commutes _ _ _ _

end Qldpc1000.Commutation
