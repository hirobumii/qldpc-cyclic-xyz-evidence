import QLDPC.Commutation.Chunk05

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l7_commute_row30 : l7.all (fun q => !((⟨9077706545431044, 9077706545431044⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row31 : l7.all (fun q => !((⟨18155413090862088, 18155413090862088⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row32 : l7.all (fun q => !((⟨36310826181724176, 36310826181724176⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row33 : l7.all (fun q => !((⟨568456103612448, 568456103612448⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row34 : l7.all (fun q => !((⟨1136912207224896, 1136912207224896⟩ : Pauli 56).symplectic q)) = true := by decide

end QLDPC.Candidates
