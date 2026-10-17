import QLDPC.Commutation.Chunk04

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l7_commute_row25 : l7.all (fun q => !((⟨0, 2533313454538896⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row26 : l7.all (fun q => !((⟨0, 4508075000086816⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row27 : l7.all (fun q => !((⟨0, 9016150000173632⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row28 : l7.all (fun q => !((⟨2269426636357761, 2269426636357761⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row29 : l7.all (fun q => !((⟨4538853272715522, 4538853272715522⟩ : Pauli 56).symplectic q)) = true := by decide

end QLDPC.Candidates
