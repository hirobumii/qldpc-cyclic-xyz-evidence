import Std

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Qldpc1000

def syndrome (column : α → Nat) : List α → Nat
  | [] => 0
  | q :: qs => column q ^^^ syndrome column qs

theorem syndrome_append (c : α → Nat) (s t : List α) :
    syndrome c (s ++ t) = syndrome c s ^^^ syndrome c t := by
  induction s with
  | nil => simp [syndrome]
  | cons a s ih => simp only [List.cons_append, syndrome, ih, Nat.xor_assoc]

theorem xor_cancel (a b : Nat) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem xor_eq_zero (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have hh := congrArg (fun x => a ^^^ x) h
    simpa [xor_cancel] using hh.symm
  · intro h; subst b; exact Nat.xor_self _

theorem syndrome_bit_exists (c : α → Nat) (s : List α) (r : Nat)
    (h : (syndrome c s).testBit r = true) :
    ∃ q ∈ s, (c q).testBit r = true := by
  induction s with
  | nil => simp [syndrome] at h
  | cons q qs ih =>
    by_cases hq : (c q).testBit r = true
    · exact ⟨q, by simp, hq⟩
    · have hz : (c q).testBit r = false := Bool.eq_false_iff.mpr hq
      have ht : (syndrome c qs).testBit r = true := by
        simpa [syndrome, hz] using h
      obtain ⟨x, hx, hb⟩ := ih ht
      exact ⟨x, by simp [hx], hb⟩

theorem syndrome_remove [DecidableEq α] (c : α → Nat) (s : List α) (q : α)
    (hq : q ∈ s) : syndrome c (s.erase q) = c q ^^^ syndrome c s := by
  induction s with
  | nil => simp at hq
  | cons a s ih =>
    by_cases ha : a = q
    · subst a
      simp [syndrome, xor_cancel]
    · have hm : q ∈ s := by simpa [ha, Ne.symm ha] using hq
      have herase : (a :: s).erase q = a :: s.erase q := by simp [ha]
      rw [herase, syndrome, ih hm]
      rw [syndrome]
      ac_rfl

theorem syndrome_congr (c d : α → Nat) (s : List α)
    (h : ∀ q ∈ s, c q = d q) : syndrome c s = syndrome d s := by
  induction s with
  | nil => rfl
  | cons q qs ih =>
    rw [syndrome, syndrome, h q (by simp), ih (by intro a ha; exact h a (by simp [ha]))]

end Qldpc1000
