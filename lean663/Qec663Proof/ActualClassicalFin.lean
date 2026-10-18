import Qec663Proof.ActualClassical

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QEC663.Finite
open QEC663.Architecture

def columnAFin (q : Fin 156) : Nat := columnA q.val
def columnBFin (q : Fin 156) : Nat := columnB q.val

theorem actual_A_fin_index_map :
    (List.finRange 156).map columnAFin = columns baseA := by decide
theorem actual_B_fin_index_map :
    (List.finRange 156).map columnBFin = columns baseB := by decide

theorem actual_A_fin_augmentation_all :
    (List.finRange 156).all (fun q => augmentation 39 (columnAFin q)) = true := by decide
theorem actual_B_fin_augmentation_all :
    (List.finRange 156).all (fun q => augmentation 39 (columnBFin q)) = true := by decide

theorem actual_A_fin_key_nodup :
    (half4Keys ((List.finRange 156).map columnAFin)).Nodup := by
  rw [actual_A_fin_index_map]
  exact checkHalf4_sound baseA actual_A_half4_check

theorem actual_B_fin_key_nodup :
    (half4Keys ((List.finRange 156).map columnBFin)).Nodup := by
  rw [actual_B_fin_index_map]
  exact checkHalf4_sound baseB actual_B_half4_check

theorem classical_min10_A_fin (s : List (Fin 156))
    (hs : s.Sublist (List.finRange 156)) (hne : s ≠ [])
    (hz : supportSyndrome columnAFin s = 0) : 10 ≤ s.length := by
  exact classical_min10_from_key_nodup 39 columnAFin (List.finRange 156)
    (by decide) actual_A_fin_key_nodup
    (fun q hq => List.all_eq_true.mp actual_A_fin_augmentation_all q hq)
    s hs hne hz

theorem classical_min10_B_fin (s : List (Fin 156))
    (hs : s.Sublist (List.finRange 156)) (hne : s ≠ [])
    (hz : supportSyndrome columnBFin s = 0) : 10 ≤ s.length := by
  exact classical_min10_from_key_nodup 39 columnBFin (List.finRange 156)
    (by decide) actual_B_fin_key_nodup
    (fun q hq => List.all_eq_true.mp actual_B_fin_augmentation_all q hq)
    s hs hne hz

#print axioms classical_min10_A_fin
#print axioms classical_min10_B_fin

end QEC663.Finite
