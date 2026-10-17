import QLDPC.DistancePairs7_4

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair7_40 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨40, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 40 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_41 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨41, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 41 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_42 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨42, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 42 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_43 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨43, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 43 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_44 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨44, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 44 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_45 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨45, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 45 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_46 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨46, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 46 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_47 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨47, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 47 a ^^^ axiscol xc7 zc7 j b) = false := by decide


end QLDPC.DistanceProof
