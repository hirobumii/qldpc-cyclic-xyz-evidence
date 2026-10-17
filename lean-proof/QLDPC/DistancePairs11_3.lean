import QLDPC.DistancePairs11_2

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair11_24 : ∀ (j : Fin 88), 24 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 24 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_25 : ∀ (j : Fin 88), 25 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 25 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_26 : ∀ (j : Fin 88), 26 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 26 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_27 : ∀ (j : Fin 88), 27 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 27 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_28 : ∀ (j : Fin 88), 28 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 28 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_29 : ∀ (j : Fin 88), 29 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 29 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_30 : ∀ (j : Fin 88), 30 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 30 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_31 : ∀ (j : Fin 88), 31 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 31 a ^^^ axiscol xc11 zc11 j b) = false := by decide


end QLDPC.DistanceProof
