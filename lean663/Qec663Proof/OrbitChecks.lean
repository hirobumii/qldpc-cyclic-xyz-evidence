import Qec663Proof.OrbitSound
import Qec663Proof.ReflectedA

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace QEC663.Orbit
open QEC663.Finite

-- Executable regressions, not proof premises: a constant syndrome cannot
-- distinguish translated singletons, while the empty support is fixed.
#guard !(stabilizerCheck (fun _ => 0) (sortSupport [0]))
#guard stabilizerCheck (fun _ => 0) (sortSupport [])

def natColumn (bases : List Nat) (q : Coord) : Nat := (columns bases)[q.val]!
-- Keep each literal table closed so native evaluation constructs it once.
def columnABits (q : Coord) : BitVec 39 := BitVec.ofNat 39 ((columns baseA)[q.val]!)
def columnBBits (q : Coord) : BitVec 39 := BitVec.ofNat 39 ((columns baseB)[q.val]!)
def columnARBits (q : Coord) : BitVec 39 := BitVec.ofNat 39 ((columns baseAR)[q.val]!)

theorem actual_A_binding : (List.finRange 156).map (natColumn baseA) = columns baseA := by decide
theorem actual_B_binding : (List.finRange 156).map (natColumn baseB) = columns baseB := by decide
theorem actual_AR_binding : (List.finRange 156).map (natColumn baseAR) = columns baseAR := by decide

theorem actual_A_equivariant : Equivariant columnABits :=
  equivariant_of_generator _ (by decide)
theorem actual_B_equivariant : Equivariant columnBBits :=
  equivariant_of_generator _ (by decide)
theorem actual_AR_equivariant : Equivariant columnARBits :=
  equivariant_of_generator _ (by decide)
-- These exact finite evaluations retain the native compiler/runtime trust boundary.
theorem actual_A_orbit_check : checkOrbit columnABits = true := by native_decide
theorem actual_B_orbit_check : checkOrbit columnBBits = true := by native_decide
theorem actual_AR_orbit_check : checkOrbit columnARBits = true := by native_decide

theorem actual_A_full_check : checkHalf4 baseA = true :=
  orbit_checkHalf4 baseA (natColumn baseA) actual_A_binding actual_A_equivariant actual_A_orbit_check
theorem actual_B_full_check : checkHalf4 baseB = true :=
  orbit_checkHalf4 baseB (natColumn baseB) actual_B_binding actual_B_equivariant actual_B_orbit_check
theorem actual_AR_full_check : checkHalf4 baseAR = true :=
  orbit_checkHalf4 baseAR (natColumn baseAR) actual_AR_binding actual_AR_equivariant actual_AR_orbit_check

#print axioms actual_A_full_check
#print axioms actual_B_full_check
#print axioms actual_AR_full_check
end QEC663.Orbit
