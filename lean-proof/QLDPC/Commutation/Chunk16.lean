import QLDPC.Commutation.Chunk15

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l11_commute_row45 : l11.all (fun q => !((⟨1209516187517835043409922, 1209516187517835043409922⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row46 : l11.all (fun q => !((⟨2419032375035670086819844, 2419032375035670086819844⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row47 : l11.all (fun q => !((⟨4838064750071340173639688, 4838064750071340173639688⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row48 : l11.all (fun q => !((⟨9676129500142680347279376, 9676129500142680347279376⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row49 : l11.all (fun q => !((⟨19352259000285360694558752, 19352259000285360694558752⟩ : Pauli 88).symplectic q)) = true := by decide

end QLDPC.Candidates
