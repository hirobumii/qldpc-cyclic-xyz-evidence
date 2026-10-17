import QLDPC.DistancePairs11_10

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QLDPC.DistanceProof
open QLDPC.Candidates

theorem pairs11_ordered : ∀ (i j : Fin 88) (a b : Fin 3), i.val < j.val →
    allowed11 (axiscol xc11 zc11 i a ^^^ axiscol xc11 zc11 j b) = false := by
  intro i
  rcases i with ⟨i, hi⟩
  match i with
  | 0 =>
    intro j a b h
    exact pair11_0 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 1 =>
    intro j a b h
    exact pair11_1 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 2 =>
    intro j a b h
    exact pair11_2 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 3 =>
    intro j a b h
    exact pair11_3 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 4 =>
    intro j a b h
    exact pair11_4 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 5 =>
    intro j a b h
    exact pair11_5 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 6 =>
    intro j a b h
    exact pair11_6 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 7 =>
    intro j a b h
    exact pair11_7 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 8 =>
    intro j a b h
    exact pair11_8 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 9 =>
    intro j a b h
    exact pair11_9 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 10 =>
    intro j a b h
    exact pair11_10 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 11 =>
    intro j a b h
    exact pair11_11 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 12 =>
    intro j a b h
    exact pair11_12 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 13 =>
    intro j a b h
    exact pair11_13 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 14 =>
    intro j a b h
    exact pair11_14 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 15 =>
    intro j a b h
    exact pair11_15 j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))
  | 16 =>
    intro j a b h
    exact pair11_16 j h a b
  | 17 =>
    intro j a b h
    exact pair11_17 j h a b
  | 18 =>
    intro j a b h
    exact pair11_18 j h a b
  | 19 =>
    intro j a b h
    exact pair11_19 j h a b
  | 20 =>
    intro j a b h
    exact pair11_20 j h a b
  | 21 =>
    intro j a b h
    exact pair11_21 j h a b
  | 22 =>
    intro j a b h
    exact pair11_22 j h a b
  | 23 =>
    intro j a b h
    exact pair11_23 j h a b
  | 24 =>
    intro j a b h
    exact pair11_24 j h a b
  | 25 =>
    intro j a b h
    exact pair11_25 j h a b
  | 26 =>
    intro j a b h
    exact pair11_26 j h a b
  | 27 =>
    intro j a b h
    exact pair11_27 j h a b
  | 28 =>
    intro j a b h
    exact pair11_28 j h a b
  | 29 =>
    intro j a b h
    exact pair11_29 j h a b
  | 30 =>
    intro j a b h
    exact pair11_30 j h a b
  | 31 =>
    intro j a b h
    exact pair11_31 j h a b
  | 32 =>
    intro j a b h
    exact pair11_32 j h a b
  | 33 =>
    intro j a b h
    exact pair11_33 j h a b
  | 34 =>
    intro j a b h
    exact pair11_34 j h a b
  | 35 =>
    intro j a b h
    exact pair11_35 j h a b
  | 36 =>
    intro j a b h
    exact pair11_36 j h a b
  | 37 =>
    intro j a b h
    exact pair11_37 j h a b
  | 38 =>
    intro j a b h
    exact pair11_38 j h a b
  | 39 =>
    intro j a b h
    exact pair11_39 j h a b
  | 40 =>
    intro j a b h
    exact pair11_40 j h a b
  | 41 =>
    intro j a b h
    exact pair11_41 j h a b
  | 42 =>
    intro j a b h
    exact pair11_42 j h a b
  | 43 =>
    intro j a b h
    exact pair11_43 j h a b
  | 44 =>
    intro j a b h
    exact pair11_44 j h a b
  | 45 =>
    intro j a b h
    exact pair11_45 j h a b
  | 46 =>
    intro j a b h
    exact pair11_46 j h a b
  | 47 =>
    intro j a b h
    exact pair11_47 j h a b
  | 48 =>
    intro j a b h
    exact pair11_48 j h a b
  | 49 =>
    intro j a b h
    exact pair11_49 j h a b
  | 50 =>
    intro j a b h
    exact pair11_50 j h a b
  | 51 =>
    intro j a b h
    exact pair11_51 j h a b
  | 52 =>
    intro j a b h
    exact pair11_52 j h a b
  | 53 =>
    intro j a b h
    exact pair11_53 j h a b
  | 54 =>
    intro j a b h
    exact pair11_54 j h a b
  | 55 =>
    intro j a b h
    exact pair11_55 j h a b
  | 56 =>
    intro j a b h
    exact pair11_56 j h a b
  | 57 =>
    intro j a b h
    exact pair11_57 j h a b
  | 58 =>
    intro j a b h
    exact pair11_58 j h a b
  | 59 =>
    intro j a b h
    exact pair11_59 j h a b
  | 60 =>
    intro j a b h
    exact pair11_60 j h a b
  | 61 =>
    intro j a b h
    exact pair11_61 j h a b
  | 62 =>
    intro j a b h
    exact pair11_62 j h a b
  | 63 =>
    intro j a b h
    exact pair11_63 j h a b
  | 64 =>
    intro j a b h
    exact pair11_64 j h a b
  | 65 =>
    intro j a b h
    exact pair11_65 j h a b
  | 66 =>
    intro j a b h
    exact pair11_66 j h a b
  | 67 =>
    intro j a b h
    exact pair11_67 j h a b
  | 68 =>
    intro j a b h
    exact pair11_68 j h a b
  | 69 =>
    intro j a b h
    exact pair11_69 j h a b
  | 70 =>
    intro j a b h
    exact pair11_70 j h a b
  | 71 =>
    intro j a b h
    exact pair11_71 j h a b
  | 72 =>
    intro j a b h
    exact pair11_72 j h a b
  | 73 =>
    intro j a b h
    exact pair11_73 j h a b
  | 74 =>
    intro j a b h
    exact pair11_74 j h a b
  | 75 =>
    intro j a b h
    exact pair11_75 j h a b
  | 76 =>
    intro j a b h
    exact pair11_76 j h a b
  | 77 =>
    intro j a b h
    exact pair11_77 j h a b
  | 78 =>
    intro j a b h
    exact pair11_78 j h a b
  | 79 =>
    intro j a b h
    exact pair11_79 j h a b
  | 80 =>
    intro j a b h
    exact pair11_80 j h a b
  | 81 =>
    intro j a b h
    exact pair11_81 j h a b
  | 82 =>
    intro j a b h
    exact pair11_82 j h a b
  | 83 =>
    intro j a b h
    exact pair11_83 j h a b
  | 84 =>
    intro j a b h
    exact pair11_84 j h a b
  | 85 =>
    intro j a b h
    exact pair11_85 j h a b
  | 86 =>
    intro j a b h
    exact pair11_86 j h a b
  | 87 =>
    intro j a b h
    exact pair11_87 j h a b
  | k + 88 => omega

theorem pairs11 : ∀ (i j : Fin 88) (a b : Fin 3), i ≠ j →
    allowed11 (axiscol xc11 zc11 i a ^^^ axiscol xc11 zc11 j b) = false := by
  intro i j a b hne
  by_cases h : i.val < j.val
  · exact pairs11_ordered i j a b h
  · have hji : j.val < i.val := by
      have hv : i.val ≠ j.val := fun hv => hne (Fin.ext hv)
      omega
    rw [BitVec.xor_comm]
    exact pairs11_ordered j i b a hji

def certificate11 : Certificate 88 55 l11 where
  xc := xc11
  zc := zc11
  row := row11
  row_mem := rows_mem11
  bind_x := bind_x11
  bind_z := bind_z11
  allowed := allowed11
  zero_allowed := zero_allowed11
  single_allowed := single_allowed11
  single_nonzero := single_nonzero11
  pair_forbidden := pairs11

theorem no_small_normalizer11 (p : Pauli 88) (hp : Normalizes l11 p) (hw : p.weight < 4) : p.weight = 0 :=
  certificate11.no_small_normalizer p hp hw

theorem lower_bound11 (p : Pauli 88) (hp : Logical l11 p) : 4 ≤ p.weight :=
  certificate11.logical_weight_ge_four p hp


end QLDPC.DistanceProof
