import Qldpc1000.VectorFacts
import Qldpc1000.Sparse
namespace Qldpc1000
/-- Decoding uses the actual low n binary coefficients. -/
def decode (n x : Nat) : Vec n := fun i => x.testBit i.val

@[simp] theorem decode_zero (n : Nat) : decode n 0 = zero := by
  funext i
  simp [decode, zero]

@[simp] theorem decode_xor (n x y : Nat) :
    decode n (x ^^^ y) = add (decode n x) (decode n y) := by
  funext i
  simp [decode, add]

/-- The bound is essential: decoding n bits alone does not detect high bits. -/
theorem decode_zero_iff {n x : Nat} (hbound : x < 2^n) :
    decode n x = zero ↔ x = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < n
    · have he := congrFun h ⟨i, hi⟩
      simpa [decode, zero] using he
    · have hn : n ≤ i := by omega
      have hpow : 2^n ≤ 2^i := Nat.pow_le_pow_right (by decide) hn
      have hx := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hbound hpow)
      simpa using hx
  · intro h
    subst x
    exact decode_zero n

/-- Any XOR of n-bit columns remains an n-bit mask. -/
theorem syndrome_bounded {Q : Type} (n : Nat) (column : Q → Nat)
    (s : List Q) (hb : ∀ q ∈ s, column q < 2^n) :
    syndrome column s < 2^n := by
  induction s with
  | nil => simp [syndrome, Nat.two_pow_pos]
  | cons q qs ih =>
    apply Nat.xor_lt_two_pow (hb q (by simp))
    apply ih
    intro a ha
    exact hb a (by simp [ha])

/-- Interpret a finite-index support as the genuine binary sum of basis vectors. -/
def ofFinSupport (s : List (Fin n)) : Vec n := ofSupport (s.map Fin.val)

/-- A linear map whose basis columns decode from the supplied masks agrees on
    every finite support with the full XOR syndrome. No truth table over all
    vectors, native evaluator, or unproved mask semantics is needed. -/
theorem decode_syndrome (f : BinaryLinearMap n m)
    (column : Fin n → Nat)
    (basis : ∀ q, f (oneHot q.val) = decode m (column q))
    (s : List (Fin n)) :
    decode m (syndrome column s) = f (ofFinSupport s) := by
  induction s with
  | nil => simp [syndrome, ofFinSupport, ofSupport, f.map_zero]
  | cons q qs ih =>
    simp only [syndrome, decode_xor, ofFinSupport, List.map_cons, ofSupport]
    rw [f.map_add, basis]
    exact congrArg (add (decode m (column q))) ih

theorem syndrome_zero_of_map_zero (f : BinaryLinearMap n m)
    (column : Fin n → Nat)
    (basis : ∀ q, f (oneHot q.val) = decode m (column q))
    (bounded : ∀ q, column q < 2^m)
    (s : List (Fin n)) (hz : f (ofFinSupport s) = zero) :
    syndrome column s = 0 := by
  apply (decode_zero_iff (syndrome_bounded m column s (fun q _ => bounded q))).mp
  rw [decode_syndrome f column basis s]
  exact hz


end Qldpc1000
