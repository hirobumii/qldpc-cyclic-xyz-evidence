import Qec663Proof.Half4
import Qec663Proof.ClassicalDistance

namespace QEC663.Architecture
open QEC663.Finite

def chooseSupports {Q : Type} (k : Nat) : List Q → List (List Q)
  | [] => if k = 0 then [[]] else []
  | x :: xs =>
    if k = 0 then [[]]
    else (chooseSupports (k - 1) xs).map (List.cons x) ++ chooseSupports k xs

def half4Supports {Q : Type} (cs : List Q) : List (List Q) :=
  (List.range 5).flatMap (fun k => chooseSupports k cs)

def supportSyndrome {Q : Type} (column : Q → Nat) : List Q → Nat
  | [] => 0
  | x :: xs => column x ^^^ supportSyndrome column xs

@[simp] theorem chooseSupports_zero {Q : Type} (xs : List Q) :
    chooseSupports 0 xs = [[]] := by
  cases xs <;> simp [chooseSupports]

/-- The finite key enumerator is exactly the image of a full support enumerator.
Repeated syndromes are deliberately retained, including multiplicity. -/
theorem chooseSupports_map_syndrome {Q : Type} (column : Q → Nat)
    (cs : List Q) (k : Nat) :
    (chooseSupports k cs).map (supportSyndrome column) =
      chooseKeys k (cs.map column) := by
  induction cs generalizing k with
  | nil => by_cases hk : k = 0 <;> simp [chooseSupports, chooseKeys, hk, supportSyndrome]
  | cons x xs ih =>
    by_cases hk : k = 0
    · simp [chooseSupports, chooseKeys, hk, supportSyndrome]
    · simp only [chooseSupports, hk, if_false, List.map_append, List.map_map,
        List.map_cons, chooseKeys]
      rw [← ih (k - 1), ← ih k]
      simp only [List.map_map, Function.comp_def, supportSyndrome]
      rfl

/-- Every subsequence appears at its exact size. -/
theorem chooseSupports_covers {Q : Type} {s cs : List Q} (h : s.Sublist cs) :
    s ∈ chooseSupports s.length cs := by
  induction h with
  | slnil => simp [chooseSupports]
  | @cons s cs x h ih =>
    by_cases hz : s.length = 0
    · have he : s = [] := List.length_eq_zero_iff.mp hz
      subst s
      simp
    · simp only [chooseSupports, hz, if_false, List.mem_append]
      exact Or.inr ih
  | @cons₂ s cs x h ih =>
    simp only [List.length_cons, chooseSupports, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel,
      List.mem_append, List.mem_map]
    exact Or.inl ⟨s, ih, rfl⟩

/-- This is full coverage of all size-at-most-four supports, with no sampling. -/
theorem half4Supports_covers {Q : Type} {s cs : List Q}
    (h : s.Sublist cs) (hlen : s.length ≤ 4) : s ∈ half4Supports cs := by
  apply List.mem_flatMap.mpr
  exact ⟨s.length, List.mem_range.mpr (by omega), chooseSupports_covers h⟩

theorem half4Supports_map_syndrome {Q : Type} (column : Q → Nat) (cs : List Q) :
    (half4Supports cs).map (supportSyndrome column) = half4Keys (cs.map column) := by
  simp only [half4Supports, half4Keys, List.map_flatMap]
  congr 1
  funext k
  exact chooseSupports_map_syndrome column cs k

/-- The exact key-list nodup proposition establishes half4 support injectivity. -/
theorem half4_injective_from_key_nodup {Q : Type}
    (column : Q → Nat) (cs : List Q)
    (checked : (half4Keys (cs.map column)).Nodup)
    (a b : List Q) (ha : a.Sublist cs) (hb : b.Sublist cs)
    (hla : a.length ≤ 4) (hlb : b.length ≤ 4)
    (he : supportSyndrome column a = supportSyndrome column b) : a = b := by
  have hn : ((half4Supports cs).map (supportSyndrome column)).Nodup := by
    rw [half4Supports_map_syndrome]
    exact checked
  exact map_nodup_injective_on (supportSyndrome column) (half4Supports cs) hn
    a (half4Supports_covers ha hla) b (half4Supports_covers hb hlb) he

end QEC663.Architecture

namespace QEC663.Architecture

theorem supportSyndrome_append {Q : Type} (column : Q → Nat) (a b : List Q) :
    supportSyndrome column (a ++ b) =
      supportSyndrome column a ^^^ supportSyndrome column b := by
  induction a with
  | nil => simp [supportSyndrome]
  | cons x xs ih => simp [supportSyndrome, ih, Nat.xor_assoc]

theorem nat_xor_zero_iff (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have hh := congrArg (fun t => a ^^^ t) h
    simpa only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero] using hh.symm
  · intro h; subst b; exact Nat.xor_self a

theorem supportSyndrome_append_zero {Q : Type} (column : Q → Nat) (a b : List Q) :
    supportSyndrome column (a ++ b) = 0 ↔
      supportSyndrome column a = supportSyndrome column b := by
  rw [supportSyndrome_append, nat_xor_zero_iff]

def augmentation (n x : Nat) : Bool :=
  match n with
  | 0 => false
  | n + 1 => x.testBit n ^^ augmentation n x

@[simp] theorem augmentation_zero (n : Nat) : augmentation n 0 = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [augmentation, ih]

theorem bool_xor_interchange (a b c d : Bool) :
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem augmentation_xor (n x y : Nat) :
    augmentation n (x ^^^ y) = (augmentation n x ^^ augmentation n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [augmentation, Nat.testBit_xor, ih]
    exact bool_xor_interchange _ _ _ _

theorem parity_succ (m : Nat) :
    decide ((m + 1) % 2 = 1) = !decide (m % 2 = 1) := by
  by_cases h : m % 2 = 0
  · have h' : (m + 1) % 2 = 1 := by omega
    have h'' : ¬m % 2 = 1 := by omega
    simp [h', h'']
  · have h' : m % 2 = 1 := by omega
    have h'' : ¬(m + 1) % 2 = 1 := by omega
    simp [h', h'']

theorem supportSyndrome_augmentation {Q : Type} (n : Nat) (column : Q → Nat)
    (s : List Q) (odd : ∀ x ∈ s, augmentation n (column x) = true) :
    augmentation n (supportSyndrome column s) = decide (s.length % 2 = 1) := by
  induction s with
  | nil => simp [supportSyndrome]
  | cons x xs ih =>
    have hx := odd x (by simp)
    have ht : ∀ y ∈ xs, augmentation n (column y) = true := by
      intro y hy
      exact odd y (by simp [hy])
    simp only [supportSyndrome, augmentation_xor, hx, Bool.true_xor,
      ih ht, List.length_cons, parity_succ]

theorem supportSyndrome_zero_even {Q : Type} (n : Nat) (column : Q → Nat)
    (s : List Q) (odd : ∀ x ∈ s, augmentation n (column x) = true)
    (hz : supportSyndrome column s = 0) : s.length % 2 = 0 := by
  have h := supportSyndrome_augmentation n column s odd
  rw [hz, augmentation_zero] at h
  have he : ¬s.length % 2 = 1 := by
    intro ho
    simp [ho] at h
  omega

/-- Fully proved classical lower bound, parameterized only by a concrete
half4 key-list result and the oddness of its actual columns. -/
theorem classical_min10_from_key_nodup {Q : Type}
    (n : Nat) (column : Q → Nat) (cs : List Q) (hcs : cs.Nodup)
    (checked : (QEC663.Finite.half4Keys (cs.map column)).Nodup)
    (odd : ∀ q ∈ cs, augmentation n (column q) = true)
    (s : List Q) (hs : s.Sublist cs) (hne : s ≠ [])
    (hz : supportSyndrome column s = 0) : 10 ≤ s.length := by
  apply half4_classical_kernel_min10 (supportSyndrome column) 0
    (fun t => t.Sublist cs)
    (fun t ht => (List.take_sublist 4 t).trans ht)
    (fun t ht => (List.drop_sublist 4 t).trans ht)
    (supportSyndrome_append_zero column)
    (fun t ht hzero => supportSyndrome_zero_even n column t
      (fun q hq => odd q (ht.mem hq)) hzero)
    (half4_injective_from_key_nodup column cs checked)
    s hs (hs.nodup hcs) hz hne

end QEC663.Architecture
