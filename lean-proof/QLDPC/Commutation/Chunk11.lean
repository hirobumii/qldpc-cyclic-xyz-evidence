import QLDPC.Commutation.Chunk10

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l11_commute_row20 : l11.all (fun q => !((⟨2417999375311503334838784, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row21 : l11.all (fun q => !((⟨4835998714611801836758016, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row22 : l11.all (fun q => !((⟨0, 302379100949033974237185⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row23 : l11.all (fun q => !((⟨0, 604758201898067948474370⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row24 : l11.all (fun q => !((⟨0, 1209516403796135896948740⟩ : Pauli 88).symplectic q)) = true := by decide

end QLDPC.Candidates
