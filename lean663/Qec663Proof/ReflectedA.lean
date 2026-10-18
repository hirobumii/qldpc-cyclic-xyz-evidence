import Qec663Proof.Half4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QEC663.Finite

-- Actual A support exponents reflected g ↦ -g modulo39.  These literal
-- bitmasks are independently bound to the physical syndrome by adversary's
-- concrete basis bridge, rather than justified by an unproved reflection rule.
def baseAR : List Nat := [68774002689, 4320264193, 8859549697, 5385490433]

def columnARFin (q : Fin 156) : Nat := (columns baseAR)[q.val]!

theorem actual_AR_columns_count : (columns baseAR).length = 156 := by decide

theorem actual_AR_fin_index_map :
    (List.finRange 156).map columnARFin = columns baseAR := by decide

end QEC663.Finite
