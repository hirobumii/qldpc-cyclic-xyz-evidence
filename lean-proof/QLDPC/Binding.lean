import QLDPC.Candidates

namespace QLDPC.Candidates

/-- No source index is lost by conversion to the finite bit-vector representation. -/
theorem supports7_in_range :
    ∀ s ∈ supports7, ∀ i ∈ s.1 ++ s.2, i < 56 := by
  have h : supports7.all (fun s => (s.1 ++ s.2).all (fun i => decide (i < 56))) = true := by decide
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem supports11_in_range :
    ∀ s ∈ supports11, ∀ i ∈ s.1 ++ s.2, i < 88 := by
  have h : supports11.all (fun s => (s.1 ++ s.2).all (fun i => decide (i < 88))) = true := by decide
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem supports7_nodup : ∀ s ∈ supports7, s.1.Nodup ∧ s.2.Nodup := by
  have h : supports7.all (fun s => decide (s.1.Nodup ∧ s.2.Nodup)) = true := by decide
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem supports11_nodup : ∀ s ∈ supports11, s.1.Nodup ∧ s.2.Nodup := by
  have h : supports11.all (fun s => decide (s.1.Nodup ∧ s.2.Nodup)) = true := by decide
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem witness7_candidate_binding :
    witness7 = Pauli.ofSupports [] [14, 21, 34, 41] := by decide

theorem witness11_candidate_binding :
    witness11 = Pauli.ofSupports [] [22, 33, 54, 65] := by decide

end QLDPC.Candidates
