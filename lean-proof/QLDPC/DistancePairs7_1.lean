import QLDPC.DistancePairs7_0

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair7_8 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨8, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 8 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_9 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨9, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 9 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_10 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨10, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 10 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_11 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨11, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 11 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_12 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨12, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 12 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_13 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨13, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 13 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_14 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨14, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 14 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_15 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨15, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 15 a ^^^ axiscol xc7 zc7 j b) = false := by decide


end QLDPC.DistanceProof
