import QLDPC.Distance
import QLDPC.RankWitness

namespace QLDPC.Candidates

/-- Exact Pauli distance of the literal 56-qubit candidate matrix. -/
theorem l7_exact_distance_four : HasDistance l7 4 :=
  ⟨DistanceProof.lower_bound7, l7_nontrivial_weight_four⟩

/-- Exact Pauli distance of the literal 88-qubit candidate matrix. -/
theorem l11_exact_distance_four : HasDistance l11 4 :=
  ⟨DistanceProof.lower_bound11, l11_nontrivial_weight_four⟩

end QLDPC.Candidates
