import Qec663Proof.OrbitChecks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace QEC663.Finite

-- Preserve the original exhaustive-check statements. Their proofs now use
-- checked cyclic representatives plus the proved coverage/stabilizer reduction.
-- The finite orbit computations still trust the native compiler/runtime.
theorem actual_A_half4_check : checkHalf4 baseA = true :=
  QEC663.Orbit.actual_A_full_check
theorem actual_B_half4_check : checkHalf4 baseB = true :=
  QEC663.Orbit.actual_B_full_check

#print axioms actual_A_half4_check
#print axioms actual_B_half4_check

end QEC663.Finite
