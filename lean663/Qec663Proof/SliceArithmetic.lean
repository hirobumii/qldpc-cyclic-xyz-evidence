import Std

set_option maxHeartbeats 2000000

/-!
Pure arithmetic reduction for four-slice C39 cross-product kernels.
This file establishes no facts about the literal candidate by itself.
The hypotheses of `four_slice_lower_bound` are the interfaces that the
classical certificate, augmentation lemma, unit maps, and short-CC
certificate must discharge.
-/
namespace Qec663.Structure

/-- At least two of the four slice weights equal one. -/
def SingletonPair (a b c d : Nat) : Prop :=
  (a = 1 ∧ b = 1) ∨ (a = 1 ∧ c = 1) ∨ (a = 1 ∧ d = 1) ∨
  (b = 1 ∧ c = 1) ∨ (b = 1 ∧ d = 1) ∨ (c = 1 ∧ d = 1)

/-- Positivity plus equal parity excludes nonzero even CC support below ten. -/
theorem short_cc_is_odd
    (t a b c d : Nat)
    (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (pa : a % 2 = t % 2) (pb : b % 2 = t % 2)
    (pc : c % 2 = t % 2) (pd : d % 2 = t % 2)
    (hshort : t + a + b + c + d < 10) : t % 2 = 1 := by
  omega

/-- Nonzero CC support can have weight at most five in any short word. -/
theorem short_cc_le_five
    (t a b c d : Nat)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hshort : t + a + b + c + d < 10) : t ≤ 5 := by
  omega

/-- Every nonzero-CC kernel word below ten needs two singleton slices. -/
theorem short_word_has_singleton_pair
    (t a b c d : Nat)
    (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (pa : a % 2 = t % 2) (pb : b % 2 = t % 2)
    (pc : c % 2 = t % 2) (pd : d % 2 = t % 2)
    (hshort : t + a + b + c + d < 10) : SingletonPair a b c d := by
  have htodd := short_cc_is_odd t a b c d ht ha hb hc hd pa pb pc pd hshort
  unfold SingletonPair
  by_cases h₁ : a = 1 <;> by_cases h₂ : b = 1 <;>
    by_cases h₃ : c = 1 <;> by_cases h₄ : d = 1 <;> omega

/--
The complete numerical reduction. Each hypothesis explicitly represents an
obligation on a concrete code; no rank assumption or general distance theorem
is used. The statement concerns nonzero physical kernel words, so it is
stronger than a quotient-only lower bound once those obligations are met.
-/
theorem four_slice_lower_bound
    (t a b c d : Nat)
    (hclassical : t = 0 →
      (a = 0 ∨ 10 ≤ a) ∧ (b = 0 ∨ 10 ≤ b) ∧
      (c = 0 ∨ 10 ≤ c) ∧ (d = 0 ∨ 10 ≤ d))
    (hinjective : t ≠ 0 → 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (hparity : a % 2 = t % 2 ∧ b % 2 = t % 2 ∧
      c % 2 = t % 2 ∧ d % 2 = t % 2)
    (hshortCC : 0 < t → t ≤ 5 → ¬ SingletonPair a b c d)
    (hnonzero : 0 < t + a + b + c + d) :
    10 ≤ t + a + b + c + d := by
  by_cases hbound : 10 ≤ t + a + b + c + d
  · exact hbound
  have hshort : t + a + b + c + d < 10 := by omega
  by_cases ht : t = 0
  · obtain ⟨ha, hb, hc, hd⟩ := hclassical ht
    omega
  · obtain ⟨ha, hb, hc, hd⟩ := hinjective ht
    obtain ⟨pa, pb, pc, pd⟩ := hparity
    have htpos : 0 < t := by omega
    have ht5 := short_cc_le_five t a b c d ha hb hc hd hshort
    exact False.elim (hshortCC htpos ht5
      (short_word_has_singleton_pair t a b c d htpos ha hb hc hd pa pb pc pd hshort))

end Qec663.Structure

namespace Qec663.Structure

/-- Two commuting target maps cannot both produce a classical singleton
syndrome if their cross-column images are disjoint. -/
theorem singleton_targets_disjoint
    {C P : Type} (g h : C → C) (column : P → C)
    (hcommute : ∀ c, h (g c) = g (h c))
    (hseparate : ∀ p q, h (column p) ≠ g (column q))
    (c : C) : ¬ ((∃ p, g c = column p) ∧ (∃ q, h c = column q)) := by
  rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
  apply hseparate p q
  rw [← hp, ← hq]
  exact hcommute c

/-- A four-slice physical kernel word; no quotient is built into this type. -/
structure FourSliceWord (S C : Type) where
  slices : Fin 4 → S
  cc : C

/-- Physical Hamming weight once the concrete coordinate partition is bound. -/
def FourSliceWord.weight {S C : Type} (wtS : S → Nat) (wtC : C → Nat)
    (w : FourSliceWord S C) : Nat :=
  wtC w.cc + wtS (w.slices 0) + wtS (w.slices 1) +
    wtS (w.slices 2) + wtS (w.slices 3)

/-- The exact slice syndrome equations required from the literal check rows. -/
def FourSliceWord.IsCycle {S C : Type} (syndrome : S → C)
    (target : Fin 4 → C → C) (w : FourSliceWord S C) : Prop :=
  ∀ i, syndrome (w.slices i) = target i w.cc

/--
Conditional structural lower distance proof for the four-slice construction.

The finite classical certificate enters only through `classicalLower`.
The much smaller cross-column certificate enters through `separate`.
`augmentation` is the odd-column parity identity. `targetNonzero` is only
injectivity at zero, not a full-row-rank distance theorem.

All literal-coordinate and Boolean linear-algebra obligations remain explicit;
this theorem alone is not a certificate for the 663-qubit JSON.
-/
theorem four_slice_cycle_lower_bound
    {S C P : Type} (zeroC : C) (wtS : S → Nat) (wtC : C → Nat)
    (syndrome : S → C) (target : Fin 4 → C → C) (column : P → C)
    (weightZero : ∀ c, wtC c = 0 ↔ c = zeroC)
    (syndromeZero : ∀ v, wtS v = 0 → syndrome v = zeroC)
    (targetZero : ∀ i, target i zeroC = zeroC)
    (targetNonzero : ∀ i c, c ≠ zeroC → target i c ≠ zeroC)
    (classicalLower : ∀ v, syndrome v = zeroC → wtS v = 0 ∨ 10 ≤ wtS v)
    (augmentation : ∀ i v c, syndrome v = target i c → wtS v % 2 = wtC c % 2)
    (singletonColumn : ∀ v, wtS v = 1 → ∃ p, syndrome v = column p)
    (commute : ∀ i j c, target j (target i c) = target i (target j c))
    (separate : ∀ i j, i ≠ j → ∀ p q,
      target j (column p) ≠ target i (column q))
    (w : FourSliceWord S C) (hcycle : w.IsCycle syndrome target)
    (hnonzero : 0 < w.weight wtS wtC) : 10 ≤ w.weight wtS wtC := by
  have sliceClassical (ht : wtC w.cc = 0) (i : Fin 4) :
      wtS (w.slices i) = 0 ∨ 10 ≤ wtS (w.slices i) := by
    apply classicalLower
    rw [hcycle i, (weightZero w.cc).mp ht, targetZero]
  have slicePositive (ht : wtC w.cc ≠ 0) (i : Fin 4) :
      0 < wtS (w.slices i) := by
    have hcc : w.cc ≠ zeroC := by
      intro h
      exact ht ((weightZero w.cc).mpr h)
    have hsynd : syndrome (w.slices i) ≠ zeroC := by
      rw [hcycle i]
      exact targetNonzero i w.cc hcc
    have : wtS (w.slices i) ≠ 0 := by
      intro hz
      exact hsynd (syndromeZero _ hz)
    omega
  have noPair (i j : Fin 4) (hij : i ≠ j) :
      ¬ (wtS (w.slices i) = 1 ∧ wtS (w.slices j) = 1) := by
    rintro ⟨hi, hj⟩
    apply singleton_targets_disjoint (target i) (target j) column
      (commute i j) (separate i j hij) w.cc
    constructor
    · obtain ⟨p, hp⟩ := singletonColumn _ hi
      exact ⟨p, (hcycle i).symm.trans hp⟩
    · obtain ⟨q, hq⟩ := singletonColumn _ hj
      exact ⟨q, (hcycle j).symm.trans hq⟩
  apply four_slice_lower_bound (wtC w.cc) (wtS (w.slices 0))
    (wtS (w.slices 1)) (wtS (w.slices 2)) (wtS (w.slices 3))
  · intro ht
    exact ⟨sliceClassical ht 0, sliceClassical ht 1,
      sliceClassical ht 2, sliceClassical ht 3⟩
  · intro ht
    exact ⟨slicePositive ht 0, slicePositive ht 1,
      slicePositive ht 2, slicePositive ht 3⟩
  · exact ⟨augmentation 0 _ _ (hcycle 0), augmentation 1 _ _ (hcycle 1),
      augmentation 2 _ _ (hcycle 2), augmentation 3 _ _ (hcycle 3)⟩
  · intro _ _ hp
    rcases hp with h | h | h | h | h | h
    · exact noPair 0 1 (by decide) h
    · exact noPair 0 2 (by decide) h
    · exact noPair 0 3 (by decide) h
    · exact noPair 1 2 (by decide) h
    · exact noPair 1 3 (by decide) h
    · exact noPair 2 3 (by decide) h
  · exact hnonzero


/-- Same structural reduction using direct disjoint singleton preimages. -/
theorem four_slice_cycle_lower_bound_of_singletons
    {S C P : Type} (zeroC : C) (wtS : S → Nat) (wtC : C → Nat)
    (syndrome : S → C) (target : Fin 4 → C → C) (column : P → C)
    (weightZero : ∀ c, wtC c = 0 ↔ c = zeroC)
    (syndromeZero : ∀ v, wtS v = 0 → syndrome v = zeroC)
    (targetZero : ∀ i, target i zeroC = zeroC)
    (targetNonzero : ∀ i c, c ≠ zeroC → target i c ≠ zeroC)
    (classicalLower : ∀ v, syndrome v = zeroC → wtS v = 0 ∨ 10 ≤ wtS v)
    (augmentation : ∀ i v c, syndrome v = target i c → wtS v % 2 = wtC c % 2)
    (singletonColumn : ∀ v, wtS v = 1 → ∃ p, syndrome v = column p)
    (singletonsExclusion : ∀ i j, i ≠ j → ∀ c p q,
      ¬ (target i c = column p ∧ target j c = column q))
    (w : FourSliceWord S C) (hcycle : w.IsCycle syndrome target)
    (hnonzero : 0 < w.weight wtS wtC) : 10 ≤ w.weight wtS wtC := by
  have sliceClassical (ht : wtC w.cc = 0) (i : Fin 4) :
      wtS (w.slices i) = 0 ∨ 10 ≤ wtS (w.slices i) := by
    apply classicalLower
    rw [hcycle i, (weightZero w.cc).mp ht, targetZero]
  have slicePositive (ht : wtC w.cc ≠ 0) (i : Fin 4) :
      0 < wtS (w.slices i) := by
    have hcc : w.cc ≠ zeroC := by
      intro h
      exact ht ((weightZero w.cc).mpr h)
    have hsynd : syndrome (w.slices i) ≠ zeroC := by
      rw [hcycle i]
      exact targetNonzero i w.cc hcc
    have : wtS (w.slices i) ≠ 0 := by
      intro hz
      exact hsynd (syndromeZero _ hz)
    omega
  have noPair (i j : Fin 4) (hij : i ≠ j) :
      ¬ (wtS (w.slices i) = 1 ∧ wtS (w.slices j) = 1) := by
    rintro ⟨hi, hj⟩
    obtain ⟨p, hp⟩ := singletonColumn _ hi
    obtain ⟨q, hq⟩ := singletonColumn _ hj
    exact singletonsExclusion i j hij w.cc p q
      ⟨(hcycle i).symm.trans hp, (hcycle j).symm.trans hq⟩
  apply four_slice_lower_bound (wtC w.cc) (wtS (w.slices 0))
    (wtS (w.slices 1)) (wtS (w.slices 2)) (wtS (w.slices 3))
  · intro ht
    exact ⟨sliceClassical ht 0, sliceClassical ht 1,
      sliceClassical ht 2, sliceClassical ht 3⟩
  · intro ht
    exact ⟨slicePositive ht 0, slicePositive ht 1,
      slicePositive ht 2, slicePositive ht 3⟩
  · exact ⟨augmentation 0 _ _ (hcycle 0), augmentation 1 _ _ (hcycle 1),
      augmentation 2 _ _ (hcycle 2), augmentation 3 _ _ (hcycle 3)⟩
  · intro _ _ hp
    rcases hp with h | h | h | h | h | h
    · exact noPair 0 1 (by decide) h
    · exact noPair 0 2 (by decide) h
    · exact noPair 0 3 (by decide) h
    · exact noPair 1 2 (by decide) h
    · exact noPair 1 3 (by decide) h
    · exact noPair 2 3 (by decide) h
  · exact hnonzero

end Qec663.Structure

#print axioms Qec663.Structure.short_cc_is_odd
#print axioms Qec663.Structure.short_word_has_singleton_pair
#print axioms Qec663.Structure.four_slice_lower_bound
#print axioms Qec663.Structure.singleton_targets_disjoint
#print axioms Qec663.Structure.four_slice_cycle_lower_bound

#print axioms Qec663.Structure.four_slice_cycle_lower_bound_of_singletons
