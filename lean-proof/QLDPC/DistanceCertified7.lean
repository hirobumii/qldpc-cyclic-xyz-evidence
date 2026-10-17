import QLDPC.DistancePairs7_6

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pairs7 : ∀ (i j : Fin 56) (a b : Fin 3), i ≠ j →
    allowed7 (axiscol xc7 zc7 i a ^^^ axiscol xc7 zc7 j b) = false := by
  intro i
  rcases i with ⟨i, hi⟩
  match i with
  | 0 => exact pair7_0
  | 1 => exact pair7_1
  | 2 => exact pair7_2
  | 3 => exact pair7_3
  | 4 => exact pair7_4
  | 5 => exact pair7_5
  | 6 => exact pair7_6
  | 7 => exact pair7_7
  | 8 => exact pair7_8
  | 9 => exact pair7_9
  | 10 => exact pair7_10
  | 11 => exact pair7_11
  | 12 => exact pair7_12
  | 13 => exact pair7_13
  | 14 => exact pair7_14
  | 15 => exact pair7_15
  | 16 => exact pair7_16
  | 17 => exact pair7_17
  | 18 => exact pair7_18
  | 19 => exact pair7_19
  | 20 => exact pair7_20
  | 21 => exact pair7_21
  | 22 => exact pair7_22
  | 23 => exact pair7_23
  | 24 => exact pair7_24
  | 25 => exact pair7_25
  | 26 => exact pair7_26
  | 27 => exact pair7_27
  | 28 => exact pair7_28
  | 29 => exact pair7_29
  | 30 => exact pair7_30
  | 31 => exact pair7_31
  | 32 => exact pair7_32
  | 33 => exact pair7_33
  | 34 => exact pair7_34
  | 35 => exact pair7_35
  | 36 => exact pair7_36
  | 37 => exact pair7_37
  | 38 => exact pair7_38
  | 39 => exact pair7_39
  | 40 => exact pair7_40
  | 41 => exact pair7_41
  | 42 => exact pair7_42
  | 43 => exact pair7_43
  | 44 => exact pair7_44
  | 45 => exact pair7_45
  | 46 => exact pair7_46
  | 47 => exact pair7_47
  | 48 => exact pair7_48
  | 49 => exact pair7_49
  | 50 => exact pair7_50
  | 51 => exact pair7_51
  | 52 => exact pair7_52
  | 53 => exact pair7_53
  | 54 => exact pair7_54
  | 55 => exact pair7_55
  | k + 56 => omega

def certificate7 : Certificate 56 35 l7 where
  xc := xc7
  zc := zc7
  row := row7
  row_mem := rows_mem7
  bind_x := bind_x7
  bind_z := bind_z7
  allowed := allowed7
  zero_allowed := zero_allowed7
  single_allowed := single_allowed7
  single_nonzero := single_nonzero7
  pair_forbidden := pairs7

theorem no_small_normalizer7 (p : Pauli 56) (hp : Normalizes l7 p) (hw : p.weight < 4) : p.weight = 0 :=
  certificate7.no_small_normalizer p hp hw

theorem lower_bound7 (p : Pauli 56) (hp : Logical l7 p) : 4 ≤ p.weight :=
  certificate7.logical_weight_ge_four p hp


end QLDPC.DistanceProof
