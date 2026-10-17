import QLDPC.DistancePairs11_9

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair11_80 : ∀ (j : Fin 88), 80 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 80 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_81 : ∀ (j : Fin 88), 81 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 81 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_82 : ∀ (j : Fin 88), 82 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 82 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_83 : ∀ (j : Fin 88), 83 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 83 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_84 : ∀ (j : Fin 88), 84 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 84 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_85 : ∀ (j : Fin 88), 85 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 85 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_86 : ∀ (j : Fin 88), 86 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 86 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_87 : ∀ (j : Fin 88), 87 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 87 a ^^^ axiscol xc11 zc11 j b) = false := by decide


end QLDPC.DistanceProof
