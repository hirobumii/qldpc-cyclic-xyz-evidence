import QLDPC.Commutation.Chunk09

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l11_commute_row15 : l11.all (fun q => !((⟨154751958867577658776223760, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row16 : l11.all (fun q => !((⟨170023641262077474504736, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row17 : l11.all (fun q => !((⟨340047282506571352899648, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row18 : l11.all (fun q => !((⟨680020814065644886556800, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row19 : l11.all (fun q => !((⟨1208999687655755960289536, 0⟩ : Pauli 88).symplectic q)) = true := by decide

end QLDPC.Candidates
