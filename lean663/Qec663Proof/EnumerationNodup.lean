import Qec663Proof.Enumeration
import Qec663Proof.CheckerSoundness

/-! Multiplicity of the original exhaustive enumerator and the converse of
its Boolean checker soundness. No finite results are assumed here. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace QEC663.Architecture
open QEC663.Finite

theorem chooseSupports_mem {Q : Type} (cs : List Q) (k : Nat) (s : List Q)
    (h : s ∈ chooseSupports k cs) : s.Sublist cs ∧ s.length = k := by
  induction cs generalizing k s with
  | nil =>
    by_cases hk : k = 0
    · simp only [chooseSupports, hk, ite_true, List.mem_singleton] at h
      subst s
      exact ⟨.slnil, hk.symm⟩
    · simp [chooseSupports, hk] at h
  | cons q qs ih =>
    by_cases hk : k = 0
    · simp only [chooseSupports, hk, ite_true, List.mem_singleton] at h
      subst s
      exact ⟨List.nil_sublist _, hk.symm⟩
    · simp only [chooseSupports, hk, ite_false, List.mem_append, List.mem_map] at h
      rcases h with ⟨t, ht, rfl⟩ | ht
      · obtain ⟨hsub, hlen⟩ := ih (k - 1) t ht
        exact ⟨hsub.cons_cons q, by simp only [List.length_cons, hlen]; omega⟩
      · obtain ⟨hsub, hlen⟩ := ih k s ht
        exact ⟨hsub.cons q, hlen⟩

theorem chooseSupports_nodup {Q : Type} (cs : List Q) (hcs : cs.Nodup) (k : Nat) :
    (chooseSupports k cs).Nodup := by
  induction cs generalizing k with
  | nil => by_cases hk : k = 0 <;> simp [chooseSupports, hk]
  | cons q qs ih =>
    obtain ⟨hq, hqs⟩ := List.nodup_cons.mp hcs
    by_cases hk : k = 0
    · simp [chooseSupports, hk]
    · simp only [chooseSupports, hk, ite_false]
      apply List.nodup_append.mpr
      refine ⟨List.pairwise_map.mpr ((ih hqs (k - 1)).imp ?_), ih hqs k, ?_⟩
      · intro a b hab he
        exact hab (List.cons.inj he).2
      · intro a ha b hb he
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
        have hsub := (chooseSupports_mem qs k b hb).1
        have hm : q ∈ b := he ▸ List.mem_cons_self
        exact hq (hsub.mem hm)

theorem half4Supports_mem {Q : Type} (cs : List Q) (s : List Q)
    (h : s ∈ half4Supports cs) : s.Sublist cs ∧ s.length ≤ 4 := by
  obtain ⟨k, hk, hs⟩ := List.mem_flatMap.mp h
  obtain ⟨hsub, hlen⟩ := chooseSupports_mem cs k s hs
  exact ⟨hsub, by have := List.mem_range.mp hk; omega⟩

theorem half4Supports_nodup {Q : Type} (cs : List Q) (hcs : cs.Nodup) :
    (half4Supports cs).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun k _ => chooseSupports_nodup cs hcs k, ?_⟩
  apply (show (List.range 5).Nodup from List.nodup_range).imp
  intro k j hne a ha b hb he
  have hla := (chooseSupports_mem cs k a ha).2
  have hlb := (chooseSupports_mem cs j b hb).2
  exact hne (hla.symm.trans ((congrArg List.length he).trans hlb))

end QEC663.Architecture

namespace QEC663.Finite

theorem strictlyIncreasing_of_pairwise (xs : List Nat) (h : xs.Pairwise (· < ·)) :
    strictlyIncreasing xs = true := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b rest =>
      obtain ⟨hh, ht⟩ := List.pairwise_cons.mp h
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (hh b (by simp)), ih ht⟩

theorem checkHalf4_complete (bases : List Nat) (h : (half4Keys (columns bases)).Nodup) :
    checkHalf4 bases = true := by
  let xs := (half4Keys (columns bases)).mergeSort (· ≤ ·)
  have hn : xs.Nodup := h.perm (List.mergeSort_perm _ _).symm
  have hl : xs.Pairwise (· ≤ ·) := by
    simpa only [decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
        (fun (a b c : Nat) hab hbc => decide_eq_true
          (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
        (half4Keys (columns bases))
  apply strictlyIncreasing_of_pairwise xs
  exact (hl.and hn).imp (fun ⟨hle, hne⟩ => Nat.lt_of_le_of_ne hle hne)

end QEC663.Finite
