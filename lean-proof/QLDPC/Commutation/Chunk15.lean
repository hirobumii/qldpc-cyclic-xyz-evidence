import QLDPC.Commutation.Chunk14

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l11_commute_row40 : l11.all (fun q => !((⟨0, 340047282506581017624704⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row41 : l11.all (fun q => !((⟨0, 680020814065664211814656⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row42 : l11.all (fun q => !((⟨0, 1208999687655786029257216⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row43 : l11.all (fun q => !((⟨0, 2417999375311572058514432⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row44 : l11.all (fun q => !((⟨604758093758917521704961, 604758093758917521704961⟩ : Pauli 88).symplectic q)) = true := by decide

end QLDPC.Candidates
