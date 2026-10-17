import QLDPC.Commutation.Chunk12

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l11_commute_row30 : l11.all (fun q => !((⟨0, 77409049842952697404719360⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row31 : l11.all (fun q => !((⟨0, 154818099685905394809438720⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row32 : l11.all (fun q => !((⟨0, 151189550483313080140800⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row33 : l11.all (fun q => !((⟨0, 4835998714611939284107265⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row34 : l11.all (fun q => !((⟨0, 9671997429223878568214530⟩ : Pauli 88).symplectic q)) = true := by decide

end QLDPC.Candidates
