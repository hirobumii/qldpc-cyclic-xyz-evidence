import QLDPC.Commutation.Chunk08

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l11_commute_row10 : l11.all (fun q => !((⟨154818099685909795004482560, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row11 : l11.all (fun q => !((⟨9671997429223603673513985, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row12 : l11.all (fun q => !((⟨19343994858447207347027970, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row13 : l11.all (fun q => !((⟨38687989716894414694055940, 0⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row14 : l11.all (fun q => !((⟨77375979433788829388111880, 0⟩ : Pauli 88).symplectic q)) = true := by decide

end QLDPC.Candidates
