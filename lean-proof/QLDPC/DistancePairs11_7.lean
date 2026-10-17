import QLDPC.DistancePairs11_6

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair11_56 : ∀ (j : Fin 88), 56 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 56 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_57 : ∀ (j : Fin 88), 57 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 57 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_58 : ∀ (j : Fin 88), 58 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 58 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_59 : ∀ (j : Fin 88), 59 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 59 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_60 : ∀ (j : Fin 88), 60 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 60 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_61 : ∀ (j : Fin 88), 61 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 61 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_62 : ∀ (j : Fin 88), 62 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 62 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_63 : ∀ (j : Fin 88), 63 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 63 a ^^^ axiscol xc11 zc11 j b) = false := by decide


end QLDPC.DistanceProof
