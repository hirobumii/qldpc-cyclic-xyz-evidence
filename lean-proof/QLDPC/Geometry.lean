import QLDPC.Candidates

namespace QLDPC

/-- Number of supplied checks with nonidentity support at a qubit. -/
def qubitDegree (S : List (Pauli n)) (i : Nat) : Nat :=
  (S.filter (fun p => p.x.getLsbD i || p.z.getLsbD i)).length

/-- Cube-block ordering is q * L + sheet; q's bits are in 4,2,1 order. -/
def cubeSupport (L v i : Nat) : List Nat :=
  (List.range 8).map fun q =>
    q * L + (i + (q / 4 % 2) * (v / 4 % 2) +
      2 * (q / 2 % 2) * (v / 2 % 2) + 3 * (q % 2) * (v % 2)) % L

/-- The five monochromatic row blocks: X000, X111, Z100, Z011, Y010. -/
def cubeChecks (L : Nat) : List (Pauli (8 * L)) :=
  ((List.range L).map fun i => Pauli.ofSupports (cubeSupport L 0 i) []) ++
  ((List.range L).map fun i => Pauli.ofSupports (cubeSupport L 7 i) []) ++
  ((List.range L).map fun i => Pauli.ofSupports [] (cubeSupport L 4 i)) ++
  ((List.range L).map fun i => Pauli.ofSupports [] (cubeSupport L 3 i)) ++
  ((List.range L).map fun i => Pauli.ofSupports (cubeSupport L 2 i) (cubeSupport L 2 i))

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Candidates

theorem l7_cube_construction : l7 = cubeChecks 7 := by decide

theorem l11_cube_construction : l11 = cubeChecks 11 := by decide

theorem l7_qubit_degree : ∀ i : Fin 56, qubitDegree l7 i.val = 5 := by decide

theorem l11_qubit_degree : ∀ i : Fin 88, qubitDegree l11 i.val = 5 := by decide

end Candidates
end QLDPC
