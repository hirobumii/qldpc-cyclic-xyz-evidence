import QLDPC.Commutation.Chunk01

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l7_commute_row10 : l7.all (fun q => !((⟨2533313449828360, 0⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row11 : l7.all (fun q => !((⟨4508074992730256, 0⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row12 : l7.all (fun q => !((⟨9016149983379744, 0⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row13 : l7.all (fun q => !((⟨18032265875456576, 0⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row14 : l7.all (fun q => !((⟨0, 1134765258326145⟩ : Pauli 56).symplectic q)) = true := by decide

end QLDPC.Candidates
