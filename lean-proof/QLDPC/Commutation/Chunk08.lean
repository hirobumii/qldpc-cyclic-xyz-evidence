import QLDPC.Commutation.Chunk07

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l11_commute_row5 : l11.all (fun q => !((⟨4838065615184681093890080, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row6 : l11.all (fun q => !((⟨9676131230369362187780160, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row7 : l11.all (fun q => !((⟨19352262460738724375560320, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row8 : l11.all (fun q => !((⟨38704524921477448751120640, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row9 : l11.all (fun q => !((⟨77409049842954897502241280, 0⟩ : Pauli 88).symplectic q)) = true := by decide

end QLDPC.Candidates
