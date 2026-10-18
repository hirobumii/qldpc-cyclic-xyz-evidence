import Qec663Proof.VectorFacts
import Qec663Proof.Enumeration

namespace Adversary663.MaskBridge
open Binding663 QEC663.Architecture

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
theorem supportSyndrome_bounded {Q : Type} (n : Nat) (column : Q → Nat)
    (s : List Q) (hb : ∀ q ∈ s, column q < 2^n) :
    supportSyndrome column s < 2^n := by
  induction s with
  | nil => simp [supportSyndrome, Nat.two_pow_pos]
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
theorem decode_supportSyndrome (f : BinaryLinearMap n m)
    (column : Fin n → Nat)
    (basis : ∀ q, f (oneHot q.val) = decode m (column q))
    (s : List (Fin n)) :
    decode m (supportSyndrome column s) = f (ofFinSupport s) := by
  induction s with
  | nil => simp [supportSyndrome, ofFinSupport, ofSupport, f.map_zero]
  | cons q qs ih =>
    simp only [supportSyndrome, decode_xor, ofFinSupport, List.map_cons, ofSupport]
    rw [f.map_add, basis]
    exact congrArg (add (decode m (column q))) ih

theorem supportSyndrome_zero_of_map_zero (f : BinaryLinearMap n m)
    (column : Fin n → Nat)
    (basis : ∀ q, f (oneHot q.val) = decode m (column q))
    (bounded : ∀ q, column q < 2^m)
    (s : List (Fin n)) (hz : f (ofFinSupport s) = zero) :
    supportSyndrome column s = 0 := by
  apply (decode_zero_iff (supportSyndrome_bounded m column s (fun q _ => bounded q))).mp
  rw [decode_supportSyndrome f column basis s]
  exact hz

#print axioms decode_zero_iff
#print axioms decode_supportSyndrome
#print axioms supportSyndrome_zero_of_map_zero
end Adversary663.MaskBridge
