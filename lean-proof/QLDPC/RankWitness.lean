import QLDPC.RankData

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QLDPC.Candidates

theorem source7_binding : List.ofFn source7 = l7 := by decide

theorem basis7_from_source : ∀ i, linComb source7 (fromSource7 i) = basis7 i := by decide

theorem source7_from_basis : ∀ i, linComb basis7 (toBasis7 i) = source7 i := by decide

theorem basis7_pivots : ∀ i j, coordinate (basis7 i) (pivots7 j) = decide (i = j) := by decide

theorem l7_basis : IsBinaryBasis l7 basis7 :=
  basis_of_certificates source7 basis7 l7 source7_binding fromSource7 toBasis7
    basis7_from_source source7_from_basis pivots7 basis7_pivots

theorem l7_rank : HasBinaryDimension l7 32 := ⟨basis7, l7_basis⟩

theorem l7_dimension : HasBinaryDimension l7 (56 - 24) := l7_rank

theorem source11_binding : List.ofFn source11 = l11 := by decide

theorem basis11_from_source : ∀ i, linComb source11 (fromSource11 i) = basis11 i := by decide

theorem source11_from_basis : ∀ i, linComb basis11 (toBasis11 i) = source11 i := by decide

theorem basis11_pivots : ∀ i j, coordinate (basis11 i) (pivots11 j) = decide (i = j) := by decide

theorem l11_basis : IsBinaryBasis l11 basis11 :=
  basis_of_certificates source11 basis11 l11 source11_binding fromSource11 toBasis11
    basis11_from_source source11_from_basis pivots11 basis11_pivots

theorem l11_rank : HasBinaryDimension l11 52 := ⟨basis11, l11_basis⟩

theorem l11_dimension : HasBinaryDimension l11 (88 - 36) := l11_rank

theorem witness7_normalizes : Normalizes l7 witness7 := by
  have h : ∀ i : Fin 35, Commutes witness7 (source7 i) := by unfold Commutes; decide
  intro p hp
  rw [← source7_binding] at hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact h i

theorem dual7_orthogonal : ∀ p ∈ l7, Commutes p dual7 := by
  have h : ∀ i : Fin 35, Commutes (source7 i) dual7 := by unfold Commutes; decide
  intro p hp
  rw [← source7_binding] at hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact h i

theorem witness7_anticommutes_dual : witness7.symplectic dual7 = true := by decide

theorem witness7_not_inSpan : ¬ InSpan l7 witness7 :=
  not_inSpan_of_anticommuting dual7 dual7_orthogonal witness7_anticommutes_dual

theorem witness7_logical : Logical l7 witness7 :=
  ⟨witness7_normalizes, witness7_not_inSpan⟩

theorem l7_nontrivial_weight_four : ∃ p, Logical l7 p ∧ p.weight = 4 :=
  ⟨witness7, witness7_logical, witness7_weight⟩

theorem witness11_normalizes : Normalizes l11 witness11 := by
  have h : ∀ i : Fin 55, Commutes witness11 (source11 i) := by unfold Commutes; decide
  intro p hp
  rw [← source11_binding] at hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact h i

theorem dual11_orthogonal : ∀ p ∈ l11, Commutes p dual11 := by
  have h : ∀ i : Fin 55, Commutes (source11 i) dual11 := by unfold Commutes; decide
  intro p hp
  rw [← source11_binding] at hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact h i

theorem witness11_anticommutes_dual : witness11.symplectic dual11 = true := by decide

theorem witness11_not_inSpan : ¬ InSpan l11 witness11 :=
  not_inSpan_of_anticommuting dual11 dual11_orthogonal witness11_anticommutes_dual

theorem witness11_logical : Logical l11 witness11 :=
  ⟨witness11_normalizes, witness11_not_inSpan⟩

theorem l11_nontrivial_weight_four : ∃ p, Logical l11 p ∧ p.weight = 4 :=
  ⟨witness11, witness11_logical, witness11_weight⟩

#print axioms l7_rank
#print axioms l11_rank
#print axioms witness7_logical
#print axioms witness11_logical

end QLDPC.Candidates
