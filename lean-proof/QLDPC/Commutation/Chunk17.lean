import QLDPC.Commutation.Chunk16

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l11_commute_row50 : l11.all (fun q => !((⟨38704518000570721389117504, 38704518000570721389117504⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row51 : l11.all (fun q => !((⟨77409036001141442778235008, 77409036001141442778235008⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row52 : l11.all (fun q => !((⟨154818072002282885556470016, 154818072002282885556470016⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row53 : l11.all (fun q => !((⟨151207970179405044515328, 151207970179405044515328⟩ : Pauli 88).symplectic q)) = true := by decide

theorem l11_commute_row54 : l11.all (fun q => !((⟨302415940358810089030656, 302415940358810089030656⟩ : Pauli 88).symplectic q)) = true := by decide

end QLDPC.Candidates
