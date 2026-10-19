import Qec663Proof.OrbitCore

/-! Every distinct support of size at most four has a translated representative.
The proof covers the empty support and supports with nontrivial stabilizers. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace QEC663.Orbit
open QEC663.Architecture

theorem act_length (r : Shift) (s : Support) : (act r s).val.length = s.val.length := by
  exact (sortSupport_perm _).length_eq.trans (List.length_map _)

theorem act_nodup (r : Shift) (s : Support) (hs : s.val.Nodup) : (act r s).val.Nodup := by
  have hm : (s.val.map (shift r)).Nodup := List.pairwise_map.mpr
    (hs.imp (fun hne he => hne (shift_injective r he)))
  exact hm.perm (sortSupport_perm _).symm

theorem mem_act (r : Shift) (s : Support) (q : Coord) :
    q ∈ (act r s).val ↔ ∃ p ∈ s.val, shift r p = q := by
  change q ∈ (sortSupport (s.val.map (shift r))).val ↔ _
  rw [(sortSupport_perm (s.val.map (shift r))).mem_iff, List.mem_map]

def block (q : Coord) : Fin 4 := ⟨q.val / 39, by have := q.isLt; omega⟩
def blockStart (b : Fin 4) : Coord := ⟨b.val * 39, by have := b.isLt; omega⟩
def anchorShift (q : Coord) : Shift := ⟨(39 - q.val % 39) % 39, Nat.mod_lt _ (by decide)⟩

theorem shift_anchor (q : Coord) : shift (anchorShift q) q = blockStart (block q) := by
  apply Fin.ext
  simp only [shift, anchorShift, blockStart, block]
  omega

theorem shift_ge_block (r : Shift) (q p : Coord) (h : q ≤ p) :
    blockStart (block q) ≤ shift r p := by
  change q.val / 39 * 39 ≤ p.val / 39 * 39 + (p.val % 39 + r.val) % 39
  change q.val ≤ p.val at h
  omega

theorem support_sublist (s : Support) (hs : s.val.Nodup) :
    s.val.Sublist (List.finRange 156) := by
  let xs := (List.finRange 156).filter (fun q => decide (q ∈ s.val))
  have hfin : (List.finRange 156).Nodup := by decide
  have hx : xs.Nodup := List.filter_sublist.nodup hfin
  have hp : s.val.Perm xs := (List.perm_ext_iff_of_nodup hs hx).mpr (by
    intro q
    simp [xs])
  have hx_sorted : xs.Pairwise (· ≤ ·) :=
    List.Pairwise.sublist (show xs.Sublist (List.finRange 156) from List.filter_sublist)
      (by decide)
  have he := sorted_unique s.property hx_sorted hp
  simpa only [← he] using (show xs.Sublist (List.finRange 156) from List.filter_sublist)

theorem head_le (s : Support) {q : Coord} {qs : List Coord}
    (he : s.val = q :: qs) (p : Coord) (hp : p ∈ s.val) : q ≤ p := by
  rw [he] at hp
  rcases List.mem_cons.mp hp with hp | hp
  · subst p; exact Std.le_refl _
  · exact (List.pairwise_cons.mp (he ▸ s.property)).1 p hp

theorem anchor_head (s : Support) {q : Coord} {qs : List Coord}
    (he : s.val = q :: qs) :
    ∃ rest, (act (anchorShift q) s).val = blockStart (block q) :: rest := by
  let a := act (anchorShift q) s
  have hm : blockStart (block q) ∈ a.val := (mem_act _ _ _).mpr
    ⟨q, by simp [he], shift_anchor q⟩
  have hall : ∀ p ∈ a.val, blockStart (block q) ≤ p := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := (mem_act _ _ _).mp hp
    exact shift_ge_block _ q u (head_le s he u hu)
  cases ha : a.val with
  | nil => simp [ha] at hm
  | cons p ps =>
    have hlo : blockStart (block q) ≤ p := hall p (by simp [ha])
    have hhi : p ≤ blockStart (block q) := head_le a ha _ hm
    have hsame : p = blockStart (block q) := Std.le_antisymm hhi hlo
    exact ⟨ps, by rw [hsame]⟩

def tailCoords (b : Fin 4) : List Coord :=
  (List.finRange 156).filter (fun q => decide (blockStart b < q))

def anchoredSupports : List Support :=
  [sortSupport []] ++ (List.finRange 4).flatMap (fun b =>
    (List.range 4).flatMap (fun k =>
      (chooseSupports k (tailCoords b)).map (fun xs => sortSupport (blockStart b :: xs))))

theorem anchored_member (s : Support) (hs : s.val.Nodup) (hlen : s.val.length ≤ 4)
    (b : Fin 4) (xs : List Coord) (he : s.val = blockStart b :: xs) :
    s ∈ anchoredSupports := by
  have htail : ∀ p ∈ xs, blockStart b < p := by
    intro p hp
    have hle : blockStart b ≤ p := head_le s he p (by simp [he, hp])
    have hne : blockStart b ≠ p := by
      intro h
      have hn := (List.nodup_cons.mp (he ▸ hs)).1
      exact hn (h ▸ hp)
    exact Fin.lt_def.mpr (by
      change (blockStart b).val ≤ p.val at hle
      have hnv : (blockStart b).val ≠ p.val := fun h => hne (Fin.ext h)
      omega)
  have hsub : xs.Sublist (tailCoords b) := by
    have whole := support_sublist s hs
    rw [he] at whole
    have tail : xs.Sublist (List.finRange 156) :=
      (List.sublist_cons_self (blockStart b) xs).trans whole
    have hf := tail.filter (fun p => decide (blockStart b < p))
    have hid : xs.filter (fun p => decide (blockStart b < p)) = xs :=
      List.filter_eq_self.mpr (fun p hp => decide_eq_true (htail p hp))
    simpa only [hid, tailCoords] using hf
  have hsize : xs.length < 4 := by rw [he] at hlen; simp only [List.length_cons] at hlen; omega
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨b, by simp, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨xs.length, List.mem_range.mpr hsize, ?_⟩
  apply List.mem_map.mpr
  refine ⟨xs, chooseSupports_covers hsub, ?_⟩
  rw [← he, sortSupport_eq]

theorem canonical_nodup (s : Support) (hs : s.val.Nodup) : (canonical s).val.Nodup := by
  obtain ⟨r, hr⟩ := canonical_member s
  rw [hr]
  exact act_nodup r s hs

theorem canonical_length (s : Support) : (canonical s).val.length = s.val.length := by
  obtain ⟨r, hr⟩ := canonical_member s
  rw [hr, act_length]

theorem canonical_anchored (s : Support) (hs : s.val.Nodup) (hlen : s.val.length ≤ 4) :
    canonical s ∈ anchoredSupports := by
  have hn := canonical_nodup s hs
  have hl : (canonical s).val.length ≤ 4 := by rw [canonical_length]; exact hlen
  cases hc : (canonical s).val with
  | nil =>
    have he : canonical s = sortSupport [] := by
      apply Subtype.ext
      simpa only [sortSupport, List.mergeSort_nil] using hc
    rw [he]
    exact List.mem_append.mpr (Or.inl (by simp))
  | cons q qs =>
    obtain ⟨rest, ha⟩ := anchor_head (canonical s) hc
    obtain ⟨r, hr⟩ := canonical_member s
    have hle : canonical s ≤ act (anchorShift q) (canonical s) := by
      calc
        canonical s ≤ act (plus (anchorShift q) r) s := canonical_le s _
        _ = act (anchorShift q) (canonical s) := by rw [hr, act_plus]
    change (canonical s).val ≤ (act (anchorShift q) (canonical s)).val at hle
    rw [hc, ha] at hle
    have hhead : q ≤ blockStart (block q) := List.left_le_left_of_cons_le_cons hle
    have he : q = blockStart (block q) := by
      apply Fin.ext
      change q.val ≤ q.val / 39 * 39 at hhead
      change q.val = q.val / 39 * 39
      omega
    apply anchored_member (canonical s) hn hl (block q) qs
    exact hc.trans (congrArg (fun head => head :: qs) he)

def representatives : List Support :=
  -- Only shifts anchoring an occupied coordinate need to be compared at runtime.
  -- Coverage below uses a full-orbit minimum, so no unproved orbit count is assumed.
  anchoredSupports.filter (fun s => s.val.all (fun q => decide (s ≤ act (anchorShift q) s)))

theorem representative_coverage (s : Support) (hs : s.val.Nodup)
    (hlen : s.val.length ≤ 4) :
    ∃ r ∈ representatives, ∃ g : Shift, s = act g r := by
  refine ⟨canonical s, ?_, ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨canonical_anchored s hs hlen, List.all_eq_true.mpr ?_⟩
    intro q _
    apply decide_eq_true
    obtain ⟨r, hr⟩ := canonical_member s
    calc
      canonical s ≤ act (plus (anchorShift q) r) s := canonical_le s _
      _ = act (anchorShift q) (canonical s) := by rw [hr, act_plus]
  · obtain ⟨r, hr⟩ := canonical_member s
    refine ⟨neg r, ?_⟩
    rw [hr, act_neg]

end QEC663.Orbit
