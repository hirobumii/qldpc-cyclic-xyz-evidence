import Qec663Proof.MaskBridge
import Qec663Proof.SingletonCertificate
import Qec663Proof.ActualClassicalFin
import Qec663Proof.Binding663.Cyclic

namespace Adversary663.ConcreteMaskBridge
open Binding663 Adversary663.MaskBridge QEC663.Finite

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def reflectedAColumn (q : Fin 156) : Nat :=
  rotate39 SingletonCertificate.ar[q.val / 39]! (q.val % 39)

theorem x_basis_pointwise : ∀ (q : Fin 156) (r : Fin 39),
    xSyndrome (oneHot q.val) r = decode 39 (columnBFin q) r := by decide

theorem z_basis_pointwise : ∀ (q : Fin 156) (r : Fin 39),
    zSyndrome (oneHot q.val) r = decode 39 (reflectedAColumn q) r := by decide

theorem x_basis : ∀ q : Fin 156,
    xSyndrome (oneHot q.val) = decode 39 (columnBFin q) := by
  intro q
  funext r
  exact x_basis_pointwise q r

theorem z_basis : ∀ q : Fin 156,
    zSyndrome (oneHot q.val) = decode 39 (reflectedAColumn q) := by
  intro q
  funext r
  exact z_basis_pointwise q r

theorem x_columns_bounded : ∀ q : Fin 156, columnBFin q < 2^39 := by decide

theorem z_columns_bounded : ∀ q : Fin 156, reflectedAColumn q < 2^39 := by decide

#print axioms x_basis
#print axioms z_basis
#print axioms x_columns_bounded
#print axioms z_columns_bounded
end Adversary663.ConcreteMaskBridge
