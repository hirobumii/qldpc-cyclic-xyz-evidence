import Qldpc1000.Bulk

namespace Qldpc1000

/-- Two binary basis atoms cancel only when their coordinates coincide. -/
theorem two_atoms (a b : Nat) (h : (2^a ^^^ 2^b) = 0) : a = b :=
  (Nat.pow_right_inj (by decide : 1 < 2)).mp ((xor_eq_zero _ _).mp h)

/-- A symbolic four-atom identity: even multiplicities give exactly one of
three pairings. No concrete vertices or supports are enumerated. -/
theorem four_atoms (a b c d : Nat)
    (h : (2^a ^^^ (2^b ^^^ (2^c ^^^ 2^d))) = 0) :
    (a=b ∧ c=d) ∨ (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have first : a=b ∨ a=c ∨ a=d := by
    by_cases hab : a=b
    · exact Or.inl hab
    by_cases hac : a=c
    · exact Or.inr (Or.inl hac)
    by_cases had : a=d
    · exact Or.inr (Or.inr had)
    have hb := congrArg (fun x : Nat => x.testBit a) h
    simp [Nat.testBit_xor, Ne.symm hab, Ne.symm hac, Ne.symm had] at hb
  rcases first with hab | hac | had
  · refine Or.inl ⟨hab, ?_⟩
    subst b
    apply two_atoms c d
    simpa [← Nat.xor_assoc] using h
  · refine Or.inr (Or.inl ⟨hac, ?_⟩)
    have he : (2^a ^^^ (2^b ^^^ (2^c ^^^ 2^d))) =
        ((2^a ^^^ 2^c) ^^^ (2^b ^^^ 2^d)) := by ac_rfl
    rw [he, hac] at h
    exact two_atoms b d (by simpa using h)
  · refine Or.inr (Or.inr ⟨had, ?_⟩)
    have he : (2^a ^^^ (2^b ^^^ (2^c ^^^ 2^d))) =
        ((2^a ^^^ 2^d) ^^^ (2^b ^^^ 2^c)) := by ac_rfl
    rw [he, had] at h
    exact two_atoms b c (by simpa using h)

/-- In a simple rectangle-free bipartite graph a nodup list of four edges
cannot have even incidence on both shores. This is purely symbolic. -/
theorem four_edges_impossible {E : Type} (left right : E → Nat) (good : E → Prop)
    (simple : ∀ a b, good a → good b → left a=left b → right a=right b → a=b)
    (rectangle : ∀ a b c d, good a → good b → good c → good d →
      left a=left b → left c=left d → right a=right c → right b=right d → a=b ∨ a=c)
    (a b c d : E) (ha : good a) (hb : good b) (hc : good c) (hd : good d)
    (nd : [a,b,c,d].Nodup)
    (hl : syndrome (fun q => 2^(left q)) [a,b,c,d] = 0)
    (hr : syndrome (fun q => 2^(right q)) [a,b,c,d] = 0) : False := by
  have hn : a≠b ∧ a≠c ∧ a≠d := by simpa using (List.nodup_cons.mp nd).1
  have lp := four_atoms (left a) (left b) (left c) (left d) (by simpa [syndrome] using hl)
  have rp := four_atoms (right a) (right b) (right c) (right d) (by simpa [syndrome] using hr)
  rcases lp with ⟨lab,lcd⟩ | ⟨lac,lbd⟩ | ⟨lad,lbc⟩
  · rcases rp with ⟨rab,rcd⟩ | ⟨rac,rbd⟩ | ⟨rad,rbc⟩
    · exact hn.1 (simple a b ha hb lab rab)
    · exact (rectangle a b c d ha hb hc hd lab lcd rac rbd).elim hn.1 hn.2.1
    · exact (rectangle a b d c ha hb hd hc lab lcd.symm rad rbc).elim hn.1 hn.2.2
  · rcases rp with ⟨rab,rcd⟩ | ⟨rac,rbd⟩ | ⟨rad,rbc⟩
    · exact (rectangle a c b d ha hc hb hd lac lbd rab rcd).elim hn.2.1 hn.1
    · exact hn.2.1 (simple a c ha hc lac rac)
    · exact (rectangle a c d b ha hc hd hb lac lbd.symm rad rbc.symm).elim hn.2.1 hn.2.2
  · rcases rp with ⟨rab,rcd⟩ | ⟨rac,rbd⟩ | ⟨rad,rbc⟩
    · exact (rectangle a d b c ha hd hb hc lad lbc rab rcd.symm).elim hn.2.2 hn.1
    · exact (rectangle a d c b ha hd hc hb lad lbc.symm rac rbd.symm).elim hn.2.2 hn.2.1
    · exact hn.2.2 (simple a d ha hd lad rad)

/-- All nonempty supports of even size at most5 are covered by the symbolic
2-edge and4-edge arguments. These are cardinality cases, not a support search. -/
theorem small_bipartite_impossible {E : Type} (left right : E → Nat) (good : E → Prop)
    (simple : ∀ a b, good a → good b → left a=left b → right a=right b → a=b)
    (rectangle : ∀ a b c d, good a → good b → good c → good d →
      left a=left b → left c=left d → right a=right c → right b=right d → a=b ∨ a=c)
    (s : List E) (nd : s.Nodup) (ne : s≠[]) (small : s.length≤5) (even : s.length%2=0)
    (goodSupport : ∀ q∈s, good q)
    (hl : syndrome (fun q => 2^(left q)) s = 0)
    (hr : syndrome (fun q => 2^(right q)) s = 0) : False := by
  cases s with
  | nil => exact ne rfl
  | cons a s =>
    cases s with
    | nil => simp at even
    | cons b s =>
      cases s with
      | nil =>
        have he := simple a b (goodSupport a (by simp)) (goodSupport b (by simp))
          (two_atoms _ _ (by simpa [syndrome] using hl))
          (two_atoms _ _ (by simpa [syndrome] using hr))
        exact (List.nodup_cons.mp nd).1 (by simp [he])
      | cons c s =>
        cases s with
        | nil => simp at even
        | cons d s =>
          cases s with
          | nil =>
            exact four_edges_impossible left right good simple rectangle a b c d
              (goodSupport a (by simp)) (goodSupport b (by simp))
              (goodSupport c (by simp)) (goodSupport d (by simp)) nd hl hr
          | cons e s =>
            have hs : s.length=0 := by simp only [List.length_cons] at small; omega
            have hz := List.eq_nil_of_length_eq_zero hs
            subst s
            simp at even

end Qldpc1000
