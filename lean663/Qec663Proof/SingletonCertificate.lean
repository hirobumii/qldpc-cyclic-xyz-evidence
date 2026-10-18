import Std

namespace Adversary663.SingletonCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Exact C39 bit representation; bit r is the coefficient of x^r.
def mask39 : Nat := 549755813887

def rotate (x r : Nat) : Nat :=
  ((x <<< (r % 39)) ||| (x >>> (39 - r % 39))) &&& mask39

def multiply (x y : Nat) : Nat :=
  (List.range 39).foldl (fun acc r =>
    if x.testBit r then acc ^^^ rotate y r else acc) 0

def reflect (x : Nat) : Nat :=
  (List.range 39).foldl (fun acc r =>
    if x.testBit r then acc ||| (1 <<< ((39 - r) % 39)) else acc) 0

def a : Array Nat := #[180233, 4292737, 4720705, 134251137]

def b : Array Nat := #[133189, 8396867, 8405509, 33619987]

def ar : Array Nat := #[68774002689, 4320264193, 8859549697, 5385490433]

def br : Array Nat := #[146301517825, 283535015937, 138546315265, 309246050305]

def xProducts : Array Nat := #[24002660973, 413863928409, 415287185967, 12115394688, 4766935748, 310851568002, 346330415300, 277132052629, 78444638468, 56695597259, 97507666701, 380341165555, 288454090981, 288986566593, 349119693441, 21886439297]

def zProducts : Array Nat := #[233301174689, 151758583936, 139793384008, 167573755075, 112850647559, 281342117394, 356822731953, 16920810179, 499454610695, 150380954890, 209767091561, 5434020491, 4332997440, 176393183491, 342416191771, 8339396769]

def aInv : Array Nat := #[38758447740, 145017708345, 457399174636, 317658437035]

def brInv : Array Nat := #[417003557291, 90189604669, 418214340431, 14208047991]

def productTableCorrect (f g table : Array Nat) : Bool :=
  (List.range 4).all fun i => (List.range 4).all fun k =>
    table[i * 4 + k]! == multiply g[i]! f[k]!

def productSeparated (table : Array Nat) : Bool :=
  (List.range 4).all fun i => (List.range 4).all fun j =>
    if i < j then
      (List.range 4).all fun k => (List.range 4).all fun l =>
        (List.range 39).all fun r =>
          table[j * 4 + k]! != rotate table[i * 4 + l]! r
    else true

theorem reflection_correct :
    ar = a.map reflect ∧ br = b.map reflect := by decide

theorem x_product_table_correct : productTableCorrect b a xProducts = true := by decide

theorem z_product_table_correct : productTableCorrect ar br zProducts = true := by decide

theorem x_product_separated : productSeparated xProducts = true := by decide

theorem z_product_separated : productSeparated zProducts = true := by decide


-- Direct finite-index interfaces for actual literal polynomial multiplication.
theorem x_relative_shift_separation :
    ∀ (i j k l : Fin 4) (r : Fin 39), i ≠ j →
      multiply a[j.val]! b[k.val]! ≠
        rotate (multiply a[i.val]! b[l.val]!) r.val := by decide

theorem z_relative_shift_separation :
    ∀ (i j k l : Fin 4) (r : Fin 39), i ≠ j →
      multiply br[j.val]! ar[k.val]! ≠
        rotate (multiply br[i.val]! ar[l.val]!) r.val := by decide

theorem x_two_sided_inverses : ∀ i : Fin 4,
    multiply a[i.val]! aInv[i.val]! = 1 ∧
    multiply aInv[i.val]! a[i.val]! = 1 := by decide

theorem z_two_sided_inverses : ∀ i : Fin 4,
    multiply br[i.val]! brInv[i.val]! = 1 ∧
    multiply brInv[i.val]! br[i.val]! = 1 := by decide

def weight39 (x : Nat) : Nat :=
  ((List.range 39).filter fun r => x.testBit r).length

theorem literal_quintic_weights : ∀ i : Fin 4,
    weight39 a[i.val]! = 5 ∧ weight39 b[i.val]! = 5 ∧
    weight39 ar[i.val]! = 5 ∧ weight39 br[i.val]! = 5 := by decide

theorem literal_masks_bounded : ∀ i : Fin 4,
    a[i.val]! ≤ mask39 ∧ b[i.val]! ≤ mask39 ∧
    ar[i.val]! ≤ mask39 ∧ br[i.val]! ≤ mask39 ∧
    aInv[i.val]! ≤ mask39 ∧ brInv[i.val]! ≤ mask39 := by decide

#print axioms x_relative_shift_separation
#print axioms z_relative_shift_separation
#print axioms x_two_sided_inverses
#print axioms z_two_sided_inverses
#print axioms literal_quintic_weights
#print axioms literal_masks_bounded

#print axioms reflection_correct
#print axioms x_product_table_correct
#print axioms z_product_table_correct
#print axioms x_product_separated
#print axioms z_product_separated

end Adversary663.SingletonCertificate
