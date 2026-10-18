import Qec663Proof.VectorSupport
import Qec663Proof.ReflectedMaskBridge
import Qec663Proof.RunReflectedA
import Qec663Proof.ConcreteAlgebra

namespace QEC663.Architecture
open Binding663 QEC663.Finite Adversary663.ConcreteMaskBridge Qec663.Structure

/-- Unconditional lower bound for the actual 39-by-156 X-syndrome map.
This theorem consumes the complete B half4 certificate and literal basis binding. -/
theorem actual_x_classical_lower (v : Vec 156) (hv : v ≠ zero)
    (hz : xSyndrome v = zero) : 10 ≤ weight v := by
  exact vector_kernel_min10_of_support_min10
    (syndromeLinear bSupports true) columnBFin
    x_basis x_columns_bounded classical_min10_B_fin v hv hz

/-- Unconditional lower bound for the actual minus-A classical sector,
using its own complete half4 table; no reflection theorem is assumed. -/
theorem actual_z_classical_lower (v : Vec 156) (hv : v ≠ zero)
    (hz : zSyndrome v = zero) : 10 ≤ weight v := by
  exact vector_kernel_min10_of_support_min10
    (syndromeLinear aSupports false) columnARFin
    z_basis_AR z_columns_AR_bounded classical_min10_AR_fin v hv hz

theorem actual_x_classical_zero_or_lower (v : Vec 156)
    (hz : xSyndrome v = zero) : weight v = 0 ∨ 10 ≤ weight v := by
  by_cases hv : v = zero
  · left
    simp [hv, weight, zero]
  · exact Or.inr (actual_x_classical_lower v hv hz)

theorem actual_z_classical_zero_or_lower (v : Vec 156)
    (hz : zSyndrome v = zero) : weight v = 0 ∨ 10 ≤ weight v := by
  by_cases hv : v = zero
  · left
    simp [hv, weight, zero]
  · exact Or.inr (actual_z_classical_lower v hv hz)

#print axioms actual_x_classical_lower
#print axioms actual_z_classical_lower
end QEC663.Architecture
