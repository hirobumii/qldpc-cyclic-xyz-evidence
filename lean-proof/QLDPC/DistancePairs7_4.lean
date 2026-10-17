import QLDPC.DistancePairs7_3

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair7_32 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨32, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 32 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_33 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨33, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 33 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_34 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨34, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 34 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_35 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨35, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 35 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_36 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨36, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 36 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_37 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨37, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 37 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_38 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨38, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 38 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_39 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨39, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 39 a ^^^ axiscol xc7 zc7 j b) = false := by decide


end QLDPC.DistanceProof
