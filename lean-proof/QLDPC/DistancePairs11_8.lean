import QLDPC.DistancePairs11_7

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair11_64 : ∀ (j : Fin 88), 64 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 64 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_65 : ∀ (j : Fin 88), 65 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 65 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_66 : ∀ (j : Fin 88), 66 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 66 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_67 : ∀ (j : Fin 88), 67 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 67 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_68 : ∀ (j : Fin 88), 68 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 68 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_69 : ∀ (j : Fin 88), 69 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 69 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_70 : ∀ (j : Fin 88), 70 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 70 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_71 : ∀ (j : Fin 88), 71 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 71 a ^^^ axiscol xc11 zc11 j b) = false := by decide


end QLDPC.DistanceProof
