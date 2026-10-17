import QLDPC.RankWitness
import QLDPC.RankCoordinates

namespace QLDPC.Candidates

/-- Every vector in the original 56-qubit row span has exactly one list of
32 binary coefficients in the certified basis. This quantifies over all vectors
and all coefficients; it is not an evaluation of a Gaussian-elimination program. -/
theorem l7_unique_coordinates :
    ∀ p, InSpan l7 p → ∃ c : Fin 32 → Bool,
      linComb basis7 c = p ∧ ∀ d, linComb basis7 d = p → d = c :=
  binaryBasis_unique_coordinates l7_basis

/-- Every vector in the original 88-qubit row span has exactly one list of
52 binary coefficients in the certified basis. -/
theorem l11_unique_coordinates :
    ∀ p, InSpan l11 p → ∃ c : Fin 52 → Bool,
      linComb basis11 c = p ∧ ∀ d, linComb basis11 d = p → d = c :=
  binaryBasis_unique_coordinates l11_basis

theorem l7_recover_coefficients (c : Fin 32 → Bool) (j : Fin 32) :
    coordinate (linComb basis7 c) (pivots7 j) = c j :=
  recover_coefficients basis7 pivots7 basis7_pivots c j

theorem l11_recover_coefficients (c : Fin 52 → Bool) (j : Fin 52) :
    coordinate (linComb basis11 c) (pivots11 j) = c j :=
  recover_coefficients basis11 pivots11 basis11_pivots c j

#print axioms l7_unique_coordinates
#print axioms l11_unique_coordinates

end QLDPC.Candidates
