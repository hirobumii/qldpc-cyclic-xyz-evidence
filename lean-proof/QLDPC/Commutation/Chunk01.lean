import QLDPC.Commutation.Chunk00

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l7_commute_row5 : l7.all (fun q => !((⟨18156244167036960, 0⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row6 : l7.all (fun q => !((⟨36312488334073920, 0⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row7 : l7.all (fun q => !((⟨36064531750913025, 0⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row8 : l7.all (fun q => !((⟨634419417319426, 0⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row9 : l7.all (fun q => !((⟨1268838568300548, 0⟩ : Pauli 56).symplectic q)) = true := by decide

end QLDPC.Candidates
