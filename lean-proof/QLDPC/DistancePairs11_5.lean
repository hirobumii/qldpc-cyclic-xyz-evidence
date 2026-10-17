import QLDPC.DistancePairs11_4

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair11_40 : ∀ (j : Fin 88), 40 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 40 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_41 : ∀ (j : Fin 88), 41 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 41 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_42 : ∀ (j : Fin 88), 42 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 42 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_43 : ∀ (j : Fin 88), 43 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 43 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_44 : ∀ (j : Fin 88), 44 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 44 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_45 : ∀ (j : Fin 88), 45 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 45 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_46 : ∀ (j : Fin 88), 46 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 46 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_47 : ∀ (j : Fin 88), 47 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 47 a ^^^ axiscol xc11 zc11 j b) = false := by decide


end QLDPC.DistanceProof
