import QLDPC.DistancePairs7_2

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair7_24 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨24, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 24 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_25 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨25, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 25 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_26 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨26, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 26 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_27 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨27, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 27 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_28 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨28, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 28 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_29 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨29, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 29 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_30 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨30, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 30 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_31 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨31, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 31 a ^^^ axiscol xc7 zc7 j b) = false := by decide


end QLDPC.DistanceProof
