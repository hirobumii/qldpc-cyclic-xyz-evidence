import Qec663Proof.Half4

namespace QEC663.Finite

theorem strictlyIncreasing_tail (a : Nat) (xs : List Nat)
    (h : strictlyIncreasing (a :: xs) = true) : strictlyIncreasing xs = true := by
  cases xs with
  | nil => rfl
  | cons b rest =>
    exact (Bool.and_eq_true_iff.mp h).2

theorem strictlyIncreasing_head : ∀ (xs : List Nat) (a : Nat),
    strictlyIncreasing (a :: xs) = true → ∀ b ∈ xs, a < b := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro a h b hb
    have ha : a < x := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have ht : strictlyIncreasing (x :: xs) = true := (Bool.and_eq_true_iff.mp h).2
    rcases List.mem_cons.mp hb with hbx | hbx
    · simpa [hbx] using ha
    · exact Nat.lt_trans ha (ih x ht b hbx)

theorem strictlyIncreasing_pairwise (xs : List Nat) :
    strictlyIncreasing xs = true → xs.Pairwise (· < ·) := by
  induction xs with
  | nil => intro _; exact .nil
  | cons a xs ih =>
    intro h
    exact List.pairwise_cons.mpr
      ⟨strictlyIncreasing_head xs a h, ih (strictlyIncreasing_tail a xs h)⟩

theorem strictlyIncreasing_nodup (xs : List Nat)
    (h : strictlyIncreasing xs = true) : xs.Nodup := by
  exact (strictlyIncreasing_pairwise xs h).imp (fun hlt => Nat.ne_of_lt hlt)

theorem checkHalf4_sound (bases : List Nat) (h : checkHalf4 bases = true) :
    (half4Keys (columns bases)).Nodup := by
  have hn := strictlyIncreasing_nodup
    ((half4Keys (columns bases)).mergeSort (· ≤ ·)) h
  exact hn.perm (List.mergeSort_perm _ _)

#print axioms checkHalf4_sound

end QEC663.Finite
