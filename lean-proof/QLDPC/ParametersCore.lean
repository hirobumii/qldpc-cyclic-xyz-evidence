import QLDPC.Rank

namespace QLDPC

/-- The usual finite binary-symplectic stabilizer parameter conditions.
`k ≤ n` prevents natural-number subtraction from silently truncating.
This statement does not define Hilbert-space phase choices or realization. -/
def HasParameters (S : List (Pauli n)) (k d : Nat) : Prop :=
  k ≤ n ∧ PairwiseCommute S ∧ HasBinaryDimension S (n - k) ∧ HasDistance S d

end QLDPC
