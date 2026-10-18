import Qec663Proof.RunHalf4
import Qec663Proof.CheckerSoundness
import Qec663Proof.Enumeration

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QEC663.Finite
open QEC663.Architecture

def columnA (q : Nat) : Nat := (columns baseA)[q]!
def columnB (q : Nat) : Nat := (columns baseB)[q]!

theorem actual_A_index_map : (List.range 156).map columnA = columns baseA := by decide
theorem actual_B_index_map : (List.range 156).map columnB = columns baseB := by decide

theorem actual_A_augmentation_all :
    (List.range 156).all (fun q => augmentation 39 (columnA q)) = true := by decide
theorem actual_B_augmentation_all :
    (List.range 156).all (fun q => augmentation 39 (columnB q)) = true := by decide

theorem actual_A_key_nodup :
    (half4Keys ((List.range 156).map columnA)).Nodup := by
  rw [actual_A_index_map]
  exact checkHalf4_sound baseA actual_A_half4_check

theorem actual_B_key_nodup :
    (half4Keys ((List.range 156).map columnB)).Nodup := by
  rw [actual_B_index_map]
  exact checkHalf4_sound baseB actual_B_half4_check

/-- An unconditional classical minimum-distance lower bound on the actual
positive A circulant columns.  `Sublist (range 156)` represents an arbitrary
sorted support, with positions rather than column values as coordinates. -/
theorem classical_min10_A (s : List Nat) (hs : s.Sublist (List.range 156))
    (hne : s ≠ []) (hz : supportSyndrome columnA s = 0) : 10 ≤ s.length := by
  exact classical_min10_from_key_nodup 39 columnA (List.range 156)
    List.nodup_range actual_A_key_nodup
    (fun q hq => List.all_eq_true.mp actual_A_augmentation_all q hq)
    s hs hne hz

/-- Unconditional classical minimum-distance lower bound on actual B columns. -/
theorem classical_min10_B (s : List Nat) (hs : s.Sublist (List.range 156))
    (hne : s ≠ []) (hz : supportSyndrome columnB s = 0) : 10 ≤ s.length := by
  exact classical_min10_from_key_nodup 39 columnB (List.range 156)
    List.nodup_range actual_B_key_nodup
    (fun q hq => List.all_eq_true.mp actual_B_augmentation_all q hq)
    s hs hne hz

#print axioms classical_min10_A
#print axioms classical_min10_B

end QEC663.Finite
