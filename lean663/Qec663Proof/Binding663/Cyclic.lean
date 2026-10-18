import Qec663Proof.Binding663.Candidate

/-! Concrete cyclic maps in precisely the conventions of the literal rows. -/
namespace Binding663

def aSupports (i : Fin 4) : List Nat :=
  if i.val = 0 then [0, 3, 14, 15, 17]
  else if i.val = 1 then [0, 7, 15, 16, 22]
  else if i.val = 2 then [0, 6, 11, 19, 22]
  else [0, 7, 9, 15, 27]

def bSupports (i : Fin 4) : List Nat :=
  if i.val = 0 then [0, 2, 6, 11, 17]
  else if i.val = 1 then [0, 1, 6, 13, 23]
  else if i.val = 2 then [0, 2, 9, 14, 23]
  else [0, 1, 4, 16, 25]

/-- `minus=true` is the r-g convention of literal Z rows. -/
def cyclicPosition (minus : Bool) (r g : Nat) : Nat :=
  if minus then (r + 39 - g) % 39 else (r + g) % 39

/-- A literal row of the 39-by-156 classical syndrome map. -/
def syndromeSupport (polys : Fin 4 → List Nat) (minus : Bool) (r : Fin 39) : List Nat :=
  (List.finRange 4).flatMap fun j =>
    (polys j).map fun g => j.val * 39 + cyclicPosition minus r.val g

/-- A literal row of a 39-by-39 cyclic polynomial map. -/
def targetSupport (poly : List Nat) (minus : Bool) (r : Fin 39) : List Nat :=
  poly.map fun g => cyclicPosition minus r.val g

def syndromeMap (polys : Fin 4 → List Nat) (minus : Bool) (v : Vec 156) : Vec 39 :=
  fun r => sparseParity (syndromeSupport polys minus r) v

def targetMap (poly : List Nat) (minus : Bool) (v : Vec 39) : Vec 39 :=
  fun r => sparseParity (targetSupport poly minus r) v

/-- X errors are constrained by literal Z checks. -/
def xSyndrome : Vec 156 → Vec 39 := syndromeMap bSupports true
def xTarget (i : Fin 4) : Vec 39 → Vec 39 := targetMap (aSupports i) true

/-- Z errors are constrained by literal X checks. -/
def zSyndrome : Vec 156 → Vec 39 := syndromeMap aSupports false
def zTarget (i : Fin 4) : Vec 39 → Vec 39 := targetMap (bSupports i) false

/-- Local X-slice coordinates have fixed k and vary over j,r. -/
def xSliceIndex (i : Fin 4) (j : Fin 156) : Fin 663 :=
  ⟨i.val * 156 + j.val, by omega⟩

/-- Local Z-slice coordinates have fixed j and vary over k,r. -/
def zSliceIndex (i : Fin 4) (j : Fin 156) : Fin 663 :=
  ⟨(j.val / 39) * 156 + i.val * 39 + j.val % 39, by
    have hj := j.isLt
    have hi := i.isLt
    have hdiv : j.val / 39 < 4 := by omega
    have hmod : j.val % 39 < 39 := Nat.mod_lt _ (by decide)
    omega⟩

def ccIndex (j : Fin 39) : Fin 663 := ⟨624 + j.val, by omega⟩

def xSlice (v : Vec 663) (i : Fin 4) : Vec 156 := fun j => v (xSliceIndex i j)
def zSlice (v : Vec 663) (i : Fin 4) : Vec 156 := fun j => v (zSliceIndex i j)
def ccPart (v : Vec 663) : Vec 39 := fun j => v (ccIndex j)

end Binding663
