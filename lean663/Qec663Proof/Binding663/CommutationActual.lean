import Qec663Proof.Binding663.Commutation

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Binding663

/-- Every literal X generator commutes with every literal Z generator. -/
theorem actualCSSCommutationCheck : cssCommutationCheck hx hz = true := by native_decide

theorem hx_rows_kernel_hz : ∀ x ∈ hx, Kernel hz (ofSupport (n := 663) x) :=
  cssCommutationCheck_sound actualCSSCommutationCheck
    (fun x hxmem => (actual_rows_are_binary_supports x
      (List.mem_append.mpr (Or.inl hxmem))).1)
    (fun z hzmem => (actual_rows_are_binary_supports z
      (List.mem_append.mpr (Or.inr hzmem))).2)

theorem hz_rows_kernel_hx : ∀ z ∈ hz, Kernel hx (ofSupport (n := 663) z) := by
  intro z hzmem x hxmem
  rw [dot_comm]
  exact hx_rows_kernel_hz x hxmem z hzmem

/-- The complete stabilizer spans, rather than just displayed rows, are
orthogonal across the two CSS sectors. -/
theorem hx_span_kernel_hz {v : Vec 663} (h : RowSpan hx v) : Kernel hz v :=
  rowSpan_in_kernel hx_rows_kernel_hz h

theorem hz_span_kernel_hx {v : Vec 663} (h : RowSpan hz v) : Kernel hx v :=
  rowSpan_in_kernel hz_rows_kernel_hx h

theorem stabilizer_spans_orthogonal {u v : Vec 663}
    (hu : RowSpan hx u) (hv : RowSpan hz v) : dot u v = false := by
  rw [dot_comm]
  exact span_annihilated (hx_span_kernel_hz hu) hv

end Binding663
