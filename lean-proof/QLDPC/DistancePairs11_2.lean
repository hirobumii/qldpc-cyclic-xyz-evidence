import QLDPC.DistancePairs11_1

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair11_16 : ∀ (j : Fin 88), 16 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 16 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_17 : ∀ (j : Fin 88), 17 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 17 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_18 : ∀ (j : Fin 88), 18 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 18 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_19 : ∀ (j : Fin 88), 19 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 19 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_20 : ∀ (j : Fin 88), 20 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 20 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_21 : ∀ (j : Fin 88), 21 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 21 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_22 : ∀ (j : Fin 88), 22 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 22 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_23 : ∀ (j : Fin 88), 23 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 23 a ^^^ axiscol xc11 zc11 j b) = false := by decide


end QLDPC.DistanceProof
