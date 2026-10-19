import Qec663Proof.OrbitChecks
import Qec663Proof.CheckerSoundness
import Qec663Proof.Enumeration

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace QEC663.Finite
open QEC663.Architecture

-- Same full-check statement, derived from the reflected-A orbit computation.
theorem actual_AR_half4_check : checkHalf4 baseAR = true :=
  QEC663.Orbit.actual_AR_full_check

theorem actual_AR_fin_augmentation_all :
    (List.finRange 156).all (fun q => augmentation 39 (columnARFin q)) = true := by decide

theorem actual_AR_fin_key_nodup :
    (half4Keys ((List.finRange 156).map columnARFin)).Nodup := by
  rw [actual_AR_fin_index_map]
  exact checkHalf4_sound baseAR actual_AR_half4_check

/-- Unconditional classical min-distance lower bound for the literal
reflected-A columns, with all small supports covered by the proved enumerator. -/
theorem classical_min10_AR_fin (s : List (Fin 156))
    (hs : s.Sublist (List.finRange 156)) (hne : s ≠ [])
    (hz : supportSyndrome columnARFin s = 0) : 10 ≤ s.length := by
  exact classical_min10_from_key_nodup 39 columnARFin (List.finRange 156)
    (by decide) actual_AR_fin_key_nodup
    (fun q hq => List.all_eq_true.mp actual_AR_fin_augmentation_all q hq)
    s hs hne hz

#print axioms actual_AR_half4_check
#print axioms classical_min10_AR_fin

end QEC663.Finite
