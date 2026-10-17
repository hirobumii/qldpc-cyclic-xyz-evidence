import QLDPC.Candidates

namespace QLDPC

def checkPairwiseCommute (S : List (Pauli n)) : Bool :=
  S.all (fun p => S.all (fun q => !(p.symplectic q)))

theorem checkPairwiseCommute_sound (S : List (Pauli n))
    (h : checkPairwiseCommute S = true) : PairwiseCommute S := by
  intro p hp q hq
  simp only [checkPairwiseCommute, List.all_eq_true, Bool.not_eq_true] at h
  have hh := h p hp q hq
  unfold Commutes
  cases hs : p.symplectic q <;> simp_all

end QLDPC
