import QLDPC.Commutation.Chunk13

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l11_commute_row35 : l11.all (fun q => !((⟨0, 19343994858447757136429060⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row36 : l11.all (fun q => !((⟨0, 38687989716895514272858120⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row37 : l11.all (fun q => !((⟨0, 77375979433791028545716240⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row38 : l11.all (fun q => !((⟨0, 154751958867582057091432480⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row39 : l11.all (fun q => !((⟨0, 170023641253290508812352⟩ : Pauli 88).symplectic q)) = true := by decide

end QLDPC.Candidates
