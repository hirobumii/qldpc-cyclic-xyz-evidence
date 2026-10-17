import QLDPC.DistancePairs11_8

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pair11_72 : ∀ (j : Fin 88), 72 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 72 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_73 : ∀ (j : Fin 88), 73 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 73 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_74 : ∀ (j : Fin 88), 74 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 74 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_75 : ∀ (j : Fin 88), 75 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 75 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_76 : ∀ (j : Fin 88), 76 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 76 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_77 : ∀ (j : Fin 88), 77 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 77 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_78 : ∀ (j : Fin 88), 78 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 78 a ^^^ axiscol xc11 zc11 j b) = false := by decide

theorem pair11_79 : ∀ (j : Fin 88), 79 < j.val → ∀ (a b : Fin 3),
    allowed11 (axiscol xc11 zc11 79 a ^^^ axiscol xc11 zc11 j b) = false := by decide


end QLDPC.DistanceProof
