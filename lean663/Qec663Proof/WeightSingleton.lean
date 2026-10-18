import Qec663Proof.Binding663.Core

namespace Qec663.Structure
open Binding663

/-- A physical vector of weight one is exactly a standard basis vector. -/
theorem weight_one_basis {n : Nat} (v : Vec n) (h : weight v = 1) :
    ∃ p : Fin n, v = oneHot p.val := by
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp h
  have hs (i : Fin n) : v i = true ↔ i = p := by
    have hmem : i ∈ (List.finRange n).filter v ↔ i = p := by
      rw [hp]
      simp
    simpa [List.finRange] using hmem
  refine ⟨p, ?_⟩
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [oneHot, decide_eq_true_eq]
  exact (hs i).trans (Fin.ext_iff)

#print axioms weight_one_basis
end Qec663.Structure
