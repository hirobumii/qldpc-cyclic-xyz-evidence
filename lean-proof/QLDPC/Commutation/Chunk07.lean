import QLDPC.Commutation.Chunk06

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l11_commute_row0 : l11.all (fun q => !((⟨151189550474521284184065, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row1 : l11.all (fun q => !((⟨302379100949042568368130, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row2 : l11.all (fun q => !((⟨604758201898085136736260, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row3 : l11.all (fun q => !((⟨1209516403796170273472520, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row4 : l11.all (fun q => !((⟨2419032807592340546945040, 0⟩ : Pauli 88).symplectic q)) = true := by decide

end QLDPC.Candidates
