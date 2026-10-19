import Qec663Proof.Half4

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace QEC663.Finite

-- Explicit computational trust tier: native_decide introduces per-computation
-- evaluation axioms in Lean 4.35. This is not a kernel-only result.
theorem actual_A_half4_check : checkHalf4 baseA = true := by native_decide
theorem actual_B_half4_check : checkHalf4 baseB = true := by native_decide

#print axioms actual_A_half4_check
#print axioms actual_B_half4_check

end QEC663.Finite
