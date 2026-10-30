import Qldpc1000.Sparse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Qldpc1000

def part (kind : α → Fin 4) (s : List α) (i : Fin 4) : List α :=
  s.filter fun q => decide (kind q = i)

theorem part_mem (kind : α → Fin 4) (s : List α) (i : Fin 4) (q : α)
    (h : q ∈ part kind s i) : kind q = i := by simpa [part] using (List.mem_filter.mp h).2

theorem part_nodup (kind : α → Fin 4) (s : List α) (i : Fin 4) (h : s.Nodup) :
    (part kind s i).Nodup := List.filter_sublist.nodup h

theorem part_lengths (kind : α → Fin 4) (s : List α) :
    (part kind s 0).length + (part kind s 1).length +
      (part kind s 2).length + (part kind s 3).length = s.length := by
  induction s with
  | nil => rfl
  | cons q qs ih =>
    have hq := (kind q).isLt
    have hcases : kind q = 0 ∨ kind q = 1 ∨ kind q = 2 ∨ kind q = 3 := by
      have h : (kind q).val = 0 ∨ (kind q).val = 1 ∨ (kind q).val = 2 ∨ (kind q).val = 3 := by omega
      rcases h with h | h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
    simp only [part] at ih ⊢
    rcases hcases with h | h | h | h <;>
      simp only [List.filter_cons, h] <;>
      simp (config := { decide := true }) only [List.length_cons, ite_true, ite_false] <;> omega

theorem syndrome_parts (kind : α → Fin 4) (c : α → Nat) (s : List α) (b : Fin 3)
    (outside : ∀ q, kind q ≠ b.castSucc → kind q ≠ 3 → c q = 0) :
    syndrome c s = syndrome c (part kind s b.castSucc) ^^^ syndrome c (part kind s 3) := by
  induction s with
  | nil => simp [syndrome, part]
  | cons q qs ih =>
    have hd : b.castSucc ≠ (3 : Fin 4) := by
      intro h
      have he := congrArg Fin.val h
      have hb := b.isLt
      simp at he
      omega
    by_cases hb : kind q = b.castSucc
    · have hc : kind q ≠ 3 := by rw [hb]; exact hd
      simp [part, hb, hd, syndrome, ih, Nat.xor_assoc]
    · by_cases hc : kind q = 3
      · simp [part, hc, Ne.symm hd, syndrome, ih]
        ac_rfl
      · simp [part, hb, hc, syndrome, outside q hb hc, ih]

theorem syndrome_bit_parity (c : α → Nat) (s : List α) (bit : Nat)
    (h : ∀ q ∈ s, (c q).testBit bit = true) :
    ((syndrome c s).testBit bit).toNat = s.length % 2 := by
  induction s with
  | nil => simp [syndrome]
  | cons q qs ih =>
    have hq := h q (by simp)
    have ht := ih (by intro a ha; exact h a (by simp [ha]))
    simp only [syndrome, Nat.testBit_xor, hq, List.length_cons]
    cases hb : (syndrome c qs).testBit bit <;> simp_all <;> omega

/-- Soboń's four CC-support cases, sharpened by the verified bipartition.
The local VV and CC hypotheses concern only one100-vertex incidence graph.
Their concrete instantiations use algebraic simplicity and absence of four-cycles.
-/
theorem structural_lower (kind : α → Fin 4) (column : Fin 3 → α → Nat)
    (vv : ∀ b s, s.Nodup → s ≠ [] → s.length ≤ 5 →
      (∀ q ∈ s, kind q = b.castSucc) → syndrome (column b) s ≠ 0)
    (cc : ∀ b s, s.Nodup → s ≠ [] → s.length ≤ 5 →
      (∀ q ∈ s, kind q = 3) → syndrome (column b) s ≠ 0)
    (marker : ∀ b q, kind q = b.castSucc ∨ kind q = 3 →
      (column b q).testBit 100 = true)
    (special : Fin 3)
    (nonedge : ∀ q u, kind q = special.castSucc → kind u = 3 →
      column special q ≠ column special u)
    (outside : ∀ b q, kind q ≠ b.castSucc → kind q ≠ 3 → column b q = 0)
    (s : List α) (nodup : s.Nodup) (nonempty : s ≠ [])
    (zero : ∀ b, syndrome (column b) s = 0) : 6 ≤ s.length := by
  by_cases large : 6 ≤ s.length
  · exact large
  have small : s.length ≤ 5 := by omega
  let p := part kind s
  have lens : (p 0).length + (p 1).length + (p 2).length + (p 3).length = s.length :=
    part_lengths kind s
  have plen : ∀ i, (p i).length ≤ 5 := by
    intro i
    exact Nat.le_trans (List.length_filter_le _ _) small
  have pn : ∀ i, (p i).Nodup := fun i => part_nodup kind s i nodup
  have pm : ∀ i q, q ∈ p i → kind q = i := fun i q h => part_mem kind s i q h
  have boundary : ∀ b, syndrome (column b) (p b.castSucc) = syndrome (column b) (p 3) := by
    intro b
    apply (xor_eq_zero _ _).mp
    rw [← syndrome_parts kind (column b) s b (outside b)]
    exact zero b
  have parity : ∀ b : Fin 3, (p b.castSucc).length % 2 = (p 3).length % 2 := by
    intro b
    have hv := syndrome_bit_parity (column b) (p b.castSucc) 100
      (by intro q h; exact marker b q (Or.inl (pm _ q h)))
    have hc := syndrome_bit_parity (column b) (p 3) 100
      (by intro q h; exact marker b q (Or.inr (pm _ q h)))
    rw [boundary b] at hv
    omega
  have par0 := parity 0
  have par1 := parity 1
  have par2 := parity 2
  change (p 0).length % 2 = (p 3).length % 2 at par0
  change (p 1).length % 2 = (p 3).length % 2 at par1
  change (p 2).length % 2 = (p 3).length % 2 at par2
  have positive : 0 < s.length := List.length_pos_iff.mpr nonempty
  have empty_cc_case (h : (p 3).length = 0) : False := by
    have hc : p 3 = [] := List.eq_nil_of_length_eq_zero h
    have he : ∀ b : Fin 3, p b.castSucc = [] := by
      intro b
      by_cases hb : p b.castSucc = []
      · exact hb
      · have hz : syndrome (column b) (p b.castSucc) = 0 := by
          rw [boundary b, hc]; rfl
        exact False.elim (vv b _ (pn _) hb (plen _) (pm _) hz)
    have h0 := congrArg List.length (he 0)
    have h1 := congrArg List.length (he 1)
    have h2 := congrArg List.length (he 2)
    change (p 0).length = 0 at h0
    change (p 1).length = 0 at h1
    change (p 2).length = 0 at h2
    omega
  have empty_vv_case (b : Fin 3) (h : (p b.castSucc).length = 0)
      (ht : 0 < (p 3).length) : False := by
    have hv : p b.castSucc = [] := List.eq_nil_of_length_eq_zero h
    have hc : p 3 ≠ [] := List.length_pos_iff.mp ht
    have hz : syndrome (column b) (p 3) = 0 := by rw [← boundary b, hv]; rfl
    exact cc b _ (pn _) hc (plen _) (pm _) hz
  by_cases h0 : (p 3).length = 0
  · exact False.elim (empty_cc_case h0)
  by_cases h1 : (p 3).length = 1
  · have hv : ∀ b : Fin 3, (p b.castSucc).length = 1 := by
      intro b
      have hb := b.isLt
      have bp := parity b
      have hc : b = 0 ∨ b = 1 ∨ b = 2 := by
        have hh : b.val = 0 ∨ b.val = 1 ∨ b.val = 2 := by omega
        rcases hh with hh | hh | hh
        · exact Or.inl (Fin.ext hh)
        · exact Or.inr (Or.inl (Fin.ext hh))
        · exact Or.inr (Or.inr (Fin.ext hh))
      rcases hc with rfl | rfl | rfl
      · change (p 0).length = 1; omega
      · change (p 1).length = 1; omega
      · change (p 2).length = 1; omega
    have singleton {l : List α} (h : l.length = 1) : ∃ a, l = [a] := by
      cases l with
      | nil => simp at h
      | cons a as =>
        have he : as = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
        exact ⟨a, by rw [he]⟩
    obtain ⟨q, hq⟩ := singleton (hv special)
    obtain ⟨u, hu⟩ := singleton h1
    have hqe : kind q = special.castSucc := pm _ q (by rw [hq]; simp)
    have hue : kind u = 3 := pm _ u (by rw [hu]; simp)
    have he := boundary special
    simp [hq, hu, syndrome] at he
    exact False.elim (nonedge q u hqe hue he)
  have ht : 0 < (p 3).length := by omega
  have he : (p 0).length = 0 ∨ (p 1).length = 0 ∨ (p 2).length = 0 := by omega
  rcases he with he | he | he
  · exact False.elim (empty_vv_case 0 he ht)
  · exact False.elim (empty_vv_case 1 he ht)
  · exact False.elim (empty_vv_case 2 he ht)

end Qldpc1000
