import QLDPC.DistancePairs7_1

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair7_16 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨16, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 16 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_17 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨17, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 17 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_18 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨18, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 18 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_19 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨19, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 19 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_20 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨20, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 20 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_21 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨21, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 21 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_22 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨22, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 22 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_23 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨23, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 23 a ^^^ axiscol xc7 zc7 j b) = false := by decide


end QLDPC.DistanceProof
