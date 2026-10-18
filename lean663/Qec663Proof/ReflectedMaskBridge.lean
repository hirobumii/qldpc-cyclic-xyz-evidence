import Qec663Proof.ConcreteMaskBridge
import Qec663Proof.ReflectedA

namespace Adversary663.ConcreteMaskBridge
open Binding663 Adversary663.MaskBridge QEC663.Finite

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem reflected_columns_match : ∀ q : Fin 156,
    reflectedAColumn q = columnARFin q := by decide

theorem z_basis_AR : ∀ q : Fin 156,
    zSyndrome (oneHot q.val) = decode 39 (columnARFin q) := by
  intro q
  rw [← reflected_columns_match q]
  exact z_basis q

theorem z_columns_AR_bounded : ∀ q : Fin 156, columnARFin q < 2^39 := by
  intro q
  rw [← reflected_columns_match q]
  exact z_columns_bounded q

#print axioms z_basis_AR
#print axioms z_columns_AR_bounded
end Adversary663.ConcreteMaskBridge
