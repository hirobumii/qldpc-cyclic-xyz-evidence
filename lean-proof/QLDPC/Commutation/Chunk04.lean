import QLDPC.Commutation.Chunk03

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l7_commute_row20 : l7.all (fun q => !((⟨0, 567382763380800⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row21 : l7.all (fun q => !((⟨0, 18032265909044225⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row22 : l7.all (fun q => !((⟨0, 36064531818088450⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row23 : l7.all (fun q => !((⟨0, 634419285331972⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row24 : l7.all (fun q => !((⟨0, 1268838570663944⟩ : Pauli 56).symplectic q)) = true := by decide

end QLDPC.Candidates
