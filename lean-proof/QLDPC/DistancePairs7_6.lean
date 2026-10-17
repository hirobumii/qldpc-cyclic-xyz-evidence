import QLDPC.DistancePairs7_5

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair7_48 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨48, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 48 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_49 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨49, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 49 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_50 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨50, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 50 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_51 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨51, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 51 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_52 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨52, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 52 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_53 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨53, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 53 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_54 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨54, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 54 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_55 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨55, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 55 a ^^^ axiscol xc7 zc7 j b) = false := by decide


end QLDPC.DistanceProof
