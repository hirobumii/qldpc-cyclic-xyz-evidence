import Qec663Proof.ConcreteUnits

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Qec663.Structure
open Binding663

private def rotate39 (x r : Nat) : Nat :=
  ((x <<< (r % 39)) ||| (x >>> (39 - r % 39))) &&& 549755813887

def xPreimageBase : Array Nat := #[369117184, 422526522863, 376949958917, 349683622898, 269668343966, 182086173905, 2197881344, 526449647538, 135895197233, 9441410, 241314103764, 65175025776, 455995839145, 72268174222, 506349946163, 21508399106]

def zPreimageBase : Array Nat := #[531015959525, 4429405886, 49774688625, 17635269936, 167109418390, 469149680709, 477872913580, 249701770895, 195282830717, 492772461171, 294686697680, 422586805905, 242192492986, 110363409948, 243505648201, 408681882462]

def preimageMask (table : Array Nat) (i : Fin 4) (p : Fin 156) : Nat :=
  rotate39 table[i.val * 4 + p.val / 39]! (p.val % 39)

-- Native computation (compiler/runtime trusted): exact bitmap binding of every concrete singleton preimage.
theorem x_preimage_bits : ∀ (i : Fin 4) (p : Fin 156) (r : Fin 39),
    xTargetInverse i (xSyndrome (oneHot p.val)) r =
      (preimageMask xPreimageBase i p).testBit r.val := by native_decide

theorem z_preimage_bits : ∀ (i : Fin 4) (p : Fin 156) (r : Fin 39),
    zTargetInverse i (zSyndrome (oneHot p.val)) r =
      (preimageMask zPreimageBase i p).testBit r.val := by native_decide

def preimageDifferenceBit (table : Array Nat) (i j : Fin 4) (p q : Fin 156) : Fin 39 :=
  ⟨Nat.log2 (preimageMask table i p ^^^ preimageMask table j q) % 39,
    Nat.mod_lt _ (by decide)⟩

-- This quantifies all 6*156*156 unordered cross-slice column pairs (both
-- orders are harmless). The witness is an actual differing output bit.
theorem x_preimage_separated : ∀ (i j : Fin 4) (p q : Fin 156), i ≠ j →
    ∃ r : Fin 39, (preimageMask xPreimageBase i p).testBit r.val ≠
      (preimageMask xPreimageBase j q).testBit r.val := by
  have h : ∀ (i j : Fin 4) (p q : Fin 156), i ≠ j →
      (preimageMask xPreimageBase i p).testBit
        (preimageDifferenceBit xPreimageBase i j p q).val ≠
      (preimageMask xPreimageBase j q).testBit
        (preimageDifferenceBit xPreimageBase i j p q).val := by native_decide
  intro i j p q hij
  exact ⟨preimageDifferenceBit xPreimageBase i j p q, h i j p q hij⟩

theorem z_preimage_separated : ∀ (i j : Fin 4) (p q : Fin 156), i ≠ j →
    ∃ r : Fin 39, (preimageMask zPreimageBase i p).testBit r.val ≠
      (preimageMask zPreimageBase j q).testBit r.val := by
  have h : ∀ (i j : Fin 4) (p q : Fin 156), i ≠ j →
      (preimageMask zPreimageBase i p).testBit
        (preimageDifferenceBit zPreimageBase i j p q).val ≠
      (preimageMask zPreimageBase j q).testBit
        (preimageDifferenceBit zPreimageBase i j p q).val := by native_decide
  intro i j p q hij
  exact ⟨preimageDifferenceBit zPreimageBase i j p q, h i j p q hij⟩

theorem x_target_singletons_excluded (i j : Fin 4) (hij : i ≠ j)
    (c : Vec 39) (p q : Fin 156) :
    ¬ (xTarget i c = xSyndrome (oneHot p.val) ∧
       xTarget j c = xSyndrome (oneHot q.val)) := by
  rintro ⟨hp,hq⟩
  obtain ⟨r,hr⟩ := x_preimage_separated i j p q hij
  apply hr
  rw [← x_preimage_bits,← x_preimage_bits]
  have hi : xTargetInverse i (xSyndrome (oneHot p.val)) = c := by
    rw [← hp,x_left_inverse]
  have hj : xTargetInverse j (xSyndrome (oneHot q.val)) = c := by
    rw [← hq,x_left_inverse]
  rw [hi,hj]

theorem z_target_singletons_excluded (i j : Fin 4) (hij : i ≠ j)
    (c : Vec 39) (p q : Fin 156) :
    ¬ (zTarget i c = zSyndrome (oneHot p.val) ∧
       zTarget j c = zSyndrome (oneHot q.val)) := by
  rintro ⟨hp,hq⟩
  obtain ⟨r,hr⟩ := z_preimage_separated i j p q hij
  apply hr
  rw [← z_preimage_bits,← z_preimage_bits]
  have hi : zTargetInverse i (zSyndrome (oneHot p.val)) = c := by
    rw [← hp,z_left_inverse]
  have hj : zTargetInverse j (zSyndrome (oneHot q.val)) = c := by
    rw [← hq,z_left_inverse]
  rw [hi,hj]

#print axioms x_target_singletons_excluded
#print axioms z_target_singletons_excluded
end Qec663.Structure
