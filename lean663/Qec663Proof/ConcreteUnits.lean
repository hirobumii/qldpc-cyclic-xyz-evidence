import Qec663Proof.ConcreteAlgebra

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Qec663.Structure
open Binding663

def aInverseSupports (i : Fin 4) : List Nat :=
  if i.val = 0 then [2, 3, 4, 5, 6, 9, 11, 12, 13, 14, 15, 17, 18, 19, 21, 25, 26, 32, 35]
  else if i.val = 1 then [0, 3, 4, 5, 8, 9, 10, 11, 12, 15, 17, 19, 20, 21, 23, 24, 25, 30, 31, 32, 37]
  else if i.val = 2 then [2, 3, 5, 6, 7, 8, 10, 15, 16, 18, 19, 20, 24, 25, 26, 27, 28, 29, 30, 33, 35, 37, 38]
  else [0, 1, 3, 5, 7, 8, 10, 12, 16, 17, 19, 21, 22, 23, 24, 26, 28, 29, 30, 31, 32, 35, 38]

def bInverseSupports (i : Fin 4) : List Nat :=
  if i.val = 0 then [0, 1, 2, 7, 11, 13, 14, 15, 17, 19, 20, 23, 25, 27, 31, 32, 34, 36, 38]
  else if i.val = 1 then [0, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 26, 29, 30, 31, 34, 35, 36, 37]
  else if i.val = 2 then [0, 1, 2, 7, 9, 11, 12, 13, 14, 15, 16, 21, 25, 26, 29, 30, 31, 33, 36, 37, 38]
  else [0, 6, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 23, 24, 27, 28, 30, 31, 33, 34, 35, 37, 38]


def xTargetInverse (i : Fin 4) : Vec 39 → Vec 39 :=
  targetMap (aInverseSupports i) true

def zTargetInverse (i : Fin 4) : Vec 39 → Vec 39 :=
  targetMap (bInverseSupports i) false

-- 4*39 basis vectors, each equality compares39 output bits; all computations
-- use native_decide; its generated evaluation axioms trust the compiler/runtime.
theorem x_inverse_on_basis : ∀ (i : Fin 4) (p : Fin 39),
    xTargetInverse i (xTarget i (oneHot p.val)) = oneHot p.val := by
  have h : ∀ (i : Fin 4) (p r : Fin 39),
      xTargetInverse i (xTarget i (oneHot p.val)) r = (oneHot p.val) r := by native_decide
  intro i p
  funext r
  exact h i p r

theorem z_inverse_on_basis : ∀ (i : Fin 4) (p : Fin 39),
    zTargetInverse i (zTarget i (oneHot p.val)) = oneHot p.val := by
  have h : ∀ (i : Fin 4) (p r : Fin 39),
      zTargetInverse i (zTarget i (oneHot p.val)) r = (oneHot p.val) r := by native_decide
  intro i p
  funext r
  exact h i p r

theorem x_left_inverse (i : Fin 4) (v : Vec 39) :
    xTargetInverse i (xTarget i v) = v := by
  exact linear_maps_equal_on_vectors
    (composeLinear (targetLinear (aInverseSupports i) true)
      (targetLinear (aSupports i) true)) identityLinear (x_inverse_on_basis i) v

theorem z_left_inverse (i : Fin 4) (v : Vec 39) :
    zTargetInverse i (zTarget i v) = v := by
  exact linear_maps_equal_on_vectors
    (composeLinear (targetLinear (bInverseSupports i) false)
      (targetLinear (bSupports i) false)) identityLinear (z_inverse_on_basis i) v

theorem x_target_zero (i : Fin 4) : xTarget i zero = zero :=
  (targetLinear (aSupports i) true).map_zero

theorem z_target_zero (i : Fin 4) : zTarget i zero = zero :=
  (targetLinear (bSupports i) false).map_zero

theorem x_target_nonzero (i : Fin 4) (v : Vec 39) (h : v ≠ zero) :
    xTarget i v ≠ zero := by
  intro hv
  apply h
  calc
    v = xTargetInverse i (xTarget i v) := (x_left_inverse i v).symm
    _ = xTargetInverse i zero := congrArg (xTargetInverse i) hv
    _ = zero := (targetLinear (aInverseSupports i) true).map_zero

theorem z_target_nonzero (i : Fin 4) (v : Vec 39) (h : v ≠ zero) :
    zTarget i v ≠ zero := by
  intro hv
  apply h
  calc
    v = zTargetInverse i (zTarget i v) := (z_left_inverse i v).symm
    _ = zTargetInverse i zero := congrArg (zTargetInverse i) hv
    _ = zero := (targetLinear (bInverseSupports i) false).map_zero

#print axioms x_left_inverse
#print axioms z_left_inverse
#print axioms x_target_nonzero
#print axioms z_target_nonzero
end Qec663.Structure
