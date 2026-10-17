import QLDPC.ParametersCore
import QLDPC.Binding
import QLDPC.Geometry
import QLDPC.Commutation
import QLDPC.RankSemantic
import QLDPC.Distance

namespace QLDPC
open Candidates

theorem xyz88_distance : HasDistance l11 4 :=
  ⟨DistanceProof.lower_bound11, l11_nontrivial_weight_four⟩

theorem xyz88_parameters : HasParameters l11 36 4 :=
  ⟨by decide, l11_pairwise_commute, l11_dimension, xyz88_distance⟩

theorem xyz88_geometry :
    l11.length = 55 ∧ (∀ p ∈ l11, p.weight = 8) ∧
    (∀ i : Fin 88, qubitDegree l11 i.val = 5) :=
  ⟨l11_row_count, l11_check_weight, l11_qubit_degree⟩

end QLDPC
