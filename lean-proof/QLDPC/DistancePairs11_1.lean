import QLDPC.DistancePairs11_0

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair11_8 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨8, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 8 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_9 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨9, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 9 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_10 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨10, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 10 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_11 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨11, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 11 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_12 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨12, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 12 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_13 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨13, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 13 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_14 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨14, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 14 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_15 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨15, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 15 a ^^^ axiscol xc11 zc11 j b) = false := by decide


end QLDPC.DistanceProof
