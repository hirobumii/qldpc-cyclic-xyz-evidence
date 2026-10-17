import QLDPC.ParametersCore
import QLDPC.Binding
import QLDPC.Geometry
import QLDPC.Commutation
import QLDPC.RankSemantic
import QLDPC.DistanceCertified7

namespace QLDPC
open Candidates

theorem xyz56_distance : HasDistance l7 4 :=
  ⟨DistanceProof.lower_bound7, l7_nontrivial_weight_four⟩

theorem xyz56_parameters : HasParameters l7 24 4 :=
  ⟨by decide, l7_pairwise_commute, l7_dimension, xyz56_distance⟩

theorem xyz56_geometry :
    l7.length = 35 ∧ (∀ p ∈ l7, p.weight = 8) ∧
    (∀ i : Fin 56, qubitDegree l7 i.val = 5) :=
  ⟨l7_row_count, l7_check_weight, l7_qubit_degree⟩

end QLDPC
