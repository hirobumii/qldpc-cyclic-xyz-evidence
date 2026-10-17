import QLDPC.DistancePairs11_3

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair11_32 : ∀ (j : Fin 88), 32 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 32 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_33 : ∀ (j : Fin 88), 33 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 33 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_34 : ∀ (j : Fin 88), 34 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 34 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_35 : ∀ (j : Fin 88), 35 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 35 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_36 : ∀ (j : Fin 88), 36 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 36 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_37 : ∀ (j : Fin 88), 37 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 37 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_38 : ∀ (j : Fin 88), 38 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 38 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_39 : ∀ (j : Fin 88), 39 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 39 a ^^^ axiscol xc11 zc11 j b) = false := by decide


end QLDPC.DistanceProof
