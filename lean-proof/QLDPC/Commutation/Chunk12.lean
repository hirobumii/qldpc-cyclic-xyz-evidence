import QLDPC.Commutation.Chunk11

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l11_commute_row25 : l11.all (fun q => !((⟨0, 2419032807592271793897480⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row26 : l11.all (fun q => !((⟨0, 4838065615184543587794960⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row27 : l11.all (fun q => !((⟨0, 9676131230369087175589920⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row28 : l11.all (fun q => !((⟨0, 19352262460738174351179840⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row29 : l11.all (fun q => !((⟨0, 38704524921476348702359680⟩ : Pauli 88).symplectic q)) = true := by decide

end QLDPC.Candidates
