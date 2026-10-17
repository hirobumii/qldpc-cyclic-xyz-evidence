import QLDPC.Commutation.Core

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l7_commute_row0 : l7.all (fun q => !((⟨567382630219905, 0⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row1 : l7.all (fun q => !((⟨1134765260439810, 0⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row2 : l7.all (fun q => !((⟨2269530520879620, 0⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row3 : l7.all (fun q => !((⟨4539061041759240, 0⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row4 : l7.all (fun q => !((⟨9078122083518480, 0⟩ : Pauli 56).symplectic q)) = true := by decide

end QLDPC.Candidates
