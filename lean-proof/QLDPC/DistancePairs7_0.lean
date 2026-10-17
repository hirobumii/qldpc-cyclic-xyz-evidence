import QLDPC.DistanceData7

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair7_0 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨0, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 0 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_1 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨1, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 1 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_2 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨2, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 2 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_3 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨3, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 3 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_4 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨4, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 4 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_5 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨5, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 5 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_6 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨6, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 6 a ^^^ axiscol xc7 zc7 j b) = false := by decide

theorem pair7_7 : ∀ (j : Fin 56) (a b : Fin 3),
    (⟨7, by decide⟩ : Fin 56) ≠ j → allowed7 (axiscol xc7 zc7 7 a ^^^ axiscol xc7 zc7 j b) = false := by decide


end QLDPC.DistanceProof
