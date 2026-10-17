import QLDPC.Basic

/-! Independent semantic regression tests. No claim about a complex Hilbert space is made here. -/
namespace QLDPCAudit
open QLDPC

private def xFirst : Pauli 2 := ⟨1, 0⟩
private def zSecond : Pauli 2 := ⟨0, 2⟩
private def independentPair : List (Pauli 2) := [xFirst, zSecond]

/-- A stabilizer span contains products not listed among the generators. -/
theorem product_in_span : InSpan independentPair (xFirst.add zSecond) := by
  apply InSpan.add
  · apply InSpan.of_mem
    simp [independentPair]
  · apply InSpan.of_mem
    simp [independentPair]

/-- Hence checking only whether a logical witness is a supplied row is unsound. -/
theorem product_not_in_generator_list : xFirst.add zSecond ∉ independentPair := by decide

/-- The Pauli support weight counts a Y site once, despite its two binary bits. -/
theorem y_support_weight : (⟨1, 1⟩ : Pauli 1).weight = 1 := by rfl

/-- Merely counting nonzero supplied rows is not dimension. -/
theorem duplicate_row_relation : (xFirst.add xFirst) = Pauli.zero := by rfl

def parityOverlap (a b : BitVec n) : Nat :=
  ((List.range n).filter (fun i => a.getLsbD i && b.getLsbD i)).length

/-- Algebraic representation i^phase X^x Z^z. -/
structure SignedBits (n : Nat) where
  x : BitVec n
  z : BitVec n
  phase : Fin 4
  deriving DecidableEq

def SignedBits.mul (a b : SignedBits n) : SignedBits n :=
  ⟨a.x ^^^ b.x, a.z ^^^ b.z,
   ⟨(a.phase.val + b.phase.val + 2 * parityOverlap a.z b.x) % 4, Nat.mod_lt _ (by decide)⟩⟩

def xx : SignedBits 2 := ⟨3, 0, 0⟩
def zz : SignedBits 2 := ⟨0, 3, 0⟩
def yy : SignedBits 2 := ⟨3, 3, 2⟩

/-- All three unsigned rows commute. -/
theorem xx_zz_yy_commute :
    Commutes (⟨3, 0⟩ : Pauli 2) ⟨0, 3⟩ ∧
    Commutes (⟨3, 0⟩ : Pauli 2) ⟨3, 3⟩ ∧
    Commutes (⟨0, 3⟩ : Pauli 2) ⟨3, 3⟩ := by
  constructor
  · rfl
  · constructor <;> rfl

/-- Their positive Hermitian representatives nevertheless multiply to -I.
Commutation alone therefore cannot justify the all-positive phase convention. -/
theorem all_plus_phase_counterexample :
    (xx.mul zz).mul yy = (⟨0, 0, 2⟩ : SignedBits 2) := by rfl

#print axioms product_in_span
#print axioms product_not_in_generator_list
#print axioms y_support_weight
#print axioms duplicate_row_relation
#print axioms xx_zz_yy_commute
#print axioms all_plus_phase_counterexample
end QLDPCAudit
