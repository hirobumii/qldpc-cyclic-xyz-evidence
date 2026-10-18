import Qec663Proof.ConcreteAlgebra

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Qec663.Integration
open Binding663 Qec663.Structure

theorem x_syndrome_parity_basis : ∀ i : Fin 156,
    parity (xSyndrome (oneHot i.val)) = parity (oneHot i.val : Vec 156) := by native_decide

theorem z_syndrome_parity_basis : ∀ i : Fin 156,
    parity (zSyndrome (oneHot i.val)) = parity (oneHot i.val : Vec 156) := by native_decide

theorem x_target_parity_basis : ∀ j : Fin 4, ∀ i : Fin 39,
    parity (xTarget j (oneHot i.val)) = parity (oneHot i.val : Vec 39) := by native_decide

theorem z_target_parity_basis : ∀ j : Fin 4, ∀ i : Fin 39,
    parity (zTarget j (oneHot i.val)) = parity (oneHot i.val : Vec 39) := by native_decide

theorem x_augmentation (i : Fin 4) (v : Vec 156) (c : Vec 39)
    (h : xSyndrome v = xTarget i c) : weight v % 2 = weight c % 2 := by
  have hs := weight_parity_of_basis (syndromeLinear bSupports true) x_syndrome_parity_basis v
  have ht := weight_parity_of_basis (targetLinear (aSupports i) true) (x_target_parity_basis i) c
  change weight (xSyndrome v) % 2 = _ at hs
  change weight (xTarget i c) % 2 = _ at ht
  rw [← hs, h, ht]

theorem z_augmentation (i : Fin 4) (v : Vec 156) (c : Vec 39)
    (h : zSyndrome v = zTarget i c) : weight v % 2 = weight c % 2 := by
  have hs := weight_parity_of_basis (syndromeLinear aSupports false) z_syndrome_parity_basis v
  have ht := weight_parity_of_basis (targetLinear (bSupports i) false) (z_target_parity_basis i) c
  change weight (zSyndrome v) % 2 = _ at hs
  change weight (zTarget i c) % 2 = _ at ht
  rw [← hs, h, ht]

#print axioms x_augmentation
#print axioms z_augmentation
end Qec663.Integration
