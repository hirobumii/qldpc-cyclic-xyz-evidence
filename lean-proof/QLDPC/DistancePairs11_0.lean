import QLDPC.DistanceData11

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair11_0 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨0, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 0 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_1 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨1, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 1 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_2 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨2, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 2 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_3 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨3, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 3 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_4 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨4, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 4 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_5 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨5, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 5 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_6 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨6, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 6 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_7 : ∀ (j : Fin 88) (a b : Fin 3),
    (⟨7, by decide⟩ : Fin 88) ≠ j → allowed11 (axiscol xc11 zc11 7 a ^^^ axiscol xc11 zc11 j b) = false := by decide


end QLDPC.DistanceProof
