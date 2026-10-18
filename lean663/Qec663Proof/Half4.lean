import Std

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Executable exact classical-half4 check.  No imported Python/C++ booleans.
The result theorem, enumeration coverage, and sort/checker soundness must all
be present before this computation can imply a distance lower bound. -/
namespace QEC663.Finite

def baseA : List Nat := [180233, 4292737, 4720705, 134251137]
def baseB : List Nat := [133189, 8396867, 8405509, 33619987]

def rotate39 (x r : Nat) : Nat :=
  let r := r % 39
  ((x <<< r) ||| (x >>> (39 - r))) &&& ((1 <<< 39) - 1)

def columns (bases : List Nat) : List Nat :=
  bases.flatMap fun x => (List.range 39).map (rotate39 x)

-- Exact k-element subsequence syndrome enumeration.  Columns are considered
-- as positions, so coincident column values are deliberately not deduplicated.
def chooseKeys (k : Nat) : List Nat → List Nat
  | [] => if k = 0 then [0] else []
  | x :: xs =>
    if k = 0 then [0]
    else (chooseKeys (k - 1) xs).map (Nat.xor x) ++ chooseKeys k xs

def half4Keys (cs : List Nat) : List Nat :=
  (List.range 5).flatMap (fun k => chooseKeys k cs)

def strictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a < b) && strictlyIncreasing (b :: rest)

def checkHalf4 (bases : List Nat) : Bool :=
  strictlyIncreasing ((half4Keys (columns bases)).mergeSort (· ≤ ·))

theorem actual_A_columns_count : (columns baseA).length = 156 := by decide
theorem actual_B_columns_count : (columns baseB).length = 156 := by decide

def bitWeight39 (x : Nat) : Nat :=
  (List.range 39).countP (fun j => x.testBit j)

-- These are kernel reductions on actual input data, separate from any large
-- native computation that might be added later.
theorem actual_A_columns_odd :
    (columns baseA).all (fun x => decide (bitWeight39 x % 2 = 1)) = true := by decide

theorem actual_B_columns_odd :
    (columns baseB).all (fun x => decide (bitWeight39 x % 2 = 1)) = true := by decide

#print axioms actual_A_columns_count
#print axioms actual_A_columns_odd

end QEC663.Finite
