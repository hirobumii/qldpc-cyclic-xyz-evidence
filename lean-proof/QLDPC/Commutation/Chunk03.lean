import QLDPC.Commutation.Chunk02

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem l7_commute_row15 : l7.all (fun q => !((⟨0, 2269530516652290⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row16 : l7.all (fun q => !((⟨0, 4539061033304580⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row17 : l7.all (fun q => !((⟨0, 9078122066609160⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row18 : l7.all (fun q => !((⟨0, 18156244133218320⟩ : Pauli 56).symplectic q)) = true := by decide

theorem l7_commute_row19 : l7.all (fun q => !((⟨0, 36312488266436640⟩ : Pauli 56).symplectic q)) = true := by decide

end QLDPC.Candidates
