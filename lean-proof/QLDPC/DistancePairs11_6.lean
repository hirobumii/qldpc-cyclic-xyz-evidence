import QLDPC.DistancePairs11_5

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair11_48 : ∀ (j : Fin 88), 48 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 48 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_49 : ∀ (j : Fin 88), 49 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 49 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_50 : ∀ (j : Fin 88), 50 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 50 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_51 : ∀ (j : Fin 88), 51 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 51 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_52 : ∀ (j : Fin 88), 52 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 52 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_53 : ∀ (j : Fin 88), 53 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 53 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_54 : ∀ (j : Fin 88), 54 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 54 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_55 : ∀ (j : Fin 88), 55 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 55 a ^^^ axiscol xc11 zc11 j b) = false := by decide


end QLDPC.DistanceProof
