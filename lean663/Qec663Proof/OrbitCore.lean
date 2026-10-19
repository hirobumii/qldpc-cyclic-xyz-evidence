import Qec663Proof.Enumeration

/-! Cyclic translation of four 39-coordinate blocks and equivariance of
39-bit syndromes. All structural laws in this module are kernel proofs. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace QEC663.Orbit

abbrev Coord := Fin 156
abbrev Shift := Fin 39
abbrev Support := {s : List Coord // s.Pairwise (· ≤ ·)}

instance (a b : Support) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.val ≤ b.val))

def plus (r s : Shift) : Shift := ⟨(r.val + s.val) % 39, Nat.mod_lt _ (by decide)⟩
def neg (r : Shift) : Shift := ⟨(39 - r.val) % 39, Nat.mod_lt _ (by decide)⟩
def shift (r : Shift) (q : Coord) : Coord :=
  ⟨q.val / 39 * 39 + (q.val % 39 + r.val) % 39, by
    have := q.isLt
    have := Nat.mod_lt (q.val % 39 + r.val) (by decide : 0 < 39)
    omega⟩

theorem shift_plus (r s : Shift) (q : Coord) :
    shift r (shift s q) = shift (plus r s) q := by
  apply Fin.ext
  simp only [shift, plus]
  have := r.isLt
  have := s.isLt
  have := q.isLt
  omega

theorem shift_neg (r : Shift) (q : Coord) : shift (neg r) (shift r q) = q := by
  apply Fin.ext
  simp only [shift, neg]
  have := r.isLt
  have := q.isLt
  omega

theorem shift_zero (q : Coord) : shift 0 q = q := by
  apply Fin.ext
  simp only [shift]
  omega

theorem shift_injective (r : Shift) : Function.Injective (shift r) := by
  intro a b h
  have := congrArg (shift (neg r)) h
  simpa only [shift_neg] using this

def sortSupport (xs : List Coord) : Support :=
  ⟨xs.mergeSort (fun a b => decide (a ≤ b)), by
    simpa only [decide_eq_true_eq] using
      List.pairwise_mergeSort
        (fun (a b c : Coord) hab hbc => decide_eq_true (show a ≤ c from Std.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact (Std.le_total : a ≤ b ∨ b ≤ a)) xs⟩

theorem sorted_unique {a b : List Coord} (ha : a.Pairwise (· ≤ ·))
    (hb : b.Pairwise (· ≤ ·)) (h : a.Perm b) : a = b :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => Std.le_antisymm hab hba) ha hb h

theorem sortSupport_perm (xs : List Coord) : (sortSupport xs).val.Perm xs :=
  List.mergeSort_perm _ _

theorem sortSupport_eq (s : Support) : sortSupport s.val = s := by
  apply Subtype.ext
  exact sorted_unique (sortSupport s.val).property s.property (sortSupport_perm s.val)

def act (r : Shift) (s : Support) : Support := sortSupport (s.val.map (shift r))

theorem act_plus (r t : Shift) (s : Support) : act r (act t s) = act (plus r t) s := by
  apply Subtype.ext
  apply sorted_unique (act r (act t s)).property (act (plus r t) s).property
  have hp := (sortSupport_perm ((act t s).val.map (shift r))).trans
    ((sortSupport_perm (s.val.map (shift t))).map (shift r))
  have he : (s.val.map (shift t)).map (shift r) = s.val.map (shift (plus r t)) := by
    simp only [List.map_map]
    congr 1
    funext q
    exact shift_plus r t q
  exact (hp.trans (List.Perm.of_eq he)).trans (sortSupport_perm _).symm

theorem act_zero (s : Support) : act 0 s = s := by
  unfold act
  have he : s.val.map (shift 0) = s.val := by
    rw [show shift 0 = (fun q => q) from funext shift_zero]
    exact List.map_id s.val
  rw [he, sortSupport_eq]

theorem act_neg (r : Shift) (s : Support) : act (neg r) (act r s) = s := by
  rw [act_plus]
  have he : plus (neg r) r = 0 := by
    apply Fin.ext
    simp only [plus, neg]
    have := r.isLt
    omega
  rw [he, act_zero]

def rotate (r : Shift) (x : BitVec 39) : BitVec 39 := x.rotateLeft r.val

theorem rotate_bit (r : Shift) (x : BitVec 39) (i : Nat) (hi : i < 39) :
    (rotate r x).getLsbD i = x.getLsbD ((i + 39 - r.val) % 39) := by
  unfold rotate
  rw [BitVec.getLsbD_rotateLeft]
  simp only [Nat.mod_eq_of_lt r.isLt]
  by_cases h : i < r.val
  · rw [ite_eq_left h]
    congr 1
    have := r.isLt
    omega
  · rw [ite_eq_right h]
    simp only [hi, decide_true, Bool.true_and]
    congr 1
    have := r.isLt
    omega

theorem rotate_plus (r s : Shift) (x : BitVec 39) :
    rotate r (rotate s x) = rotate (plus r s) x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [rotate_bit r _ i hi, rotate_bit s _ _ (Nat.mod_lt _ (by decide)),
    rotate_bit (plus r s) _ i hi]
  congr 1
  simp only [plus]
  have := r.isLt
  have := s.isLt
  omega

theorem rotate_zero (x : BitVec 39) : rotate 0 x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [rotate_bit 0 x i hi]
  congr 1
  omega

theorem rotate_neg (r : Shift) (x : BitVec 39) : rotate (neg r) (rotate r x) = x := by
  rw [rotate_plus]
  have he : plus (neg r) r = 0 := by
    apply Fin.ext
    simp only [plus, neg]
    have := r.isLt
    omega
  rw [he, rotate_zero]

theorem rotate_xor (r : Shift) (x y : BitVec 39) :
    rotate r (x ^^^ y) = rotate r x ^^^ rotate r y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, rotate_bit r _ i hi]

theorem rotate_empty (r : Shift) : rotate r 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [rotate_bit r 0 i hi]
  simp

attribute [local instance] Min.leftLeaningOfLE

def pickMin {α : Type} [Min α] (a : α) (xs : List α) : α := (a :: xs).min?.getD a

theorem pickMin_spec {α : Type} [LE α] [Min α] [Std.IsLinearOrder α]
    [Std.LawfulOrderMin α] (a : α) (xs : List α) :
    pickMin a xs ∈ a :: xs ∧ ∀ b ∈ a :: xs, pickMin a xs ≤ b := by
  have hn := List.isSome_min?_of_ne_nil (show a :: xs ≠ [] by simp)
  cases he : (a :: xs).min? with
  | none => simp [he] at hn
  | some b => simpa only [pickMin, he, Option.getD_some] using List.min?_eq_some_iff.mp he

def canonical (s : Support) : Support := pickMin s ((List.finRange 39).map (act · s))

theorem canonical_member (s : Support) : ∃ r, canonical s = act r s := by
  rcases List.mem_cons.mp (pickMin_spec s ((List.finRange 39).map (act · s))).1 with h | h
  · exact ⟨0, h.trans (act_zero s).symm⟩
  · obtain ⟨r, _, hr⟩ := List.mem_map.mp h
    exact ⟨r, hr.symm⟩

theorem canonical_le (s : Support) (r : Shift) : canonical s ≤ act r s :=
  (pickMin_spec s ((List.finRange 39).map (act · s))).2 _
    (List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨r, by simp, rfl⟩)))

theorem canonical_idempotent (s : Support) : canonical (canonical s) = canonical s := by
  apply Std.le_antisymm
  · exact (pickMin_spec (canonical s) ((List.finRange 39).map (act · (canonical s)))).2 _ (List.mem_cons_self)
  · obtain ⟨r, hr⟩ := canonical_member s
    obtain ⟨t, ht⟩ := canonical_member (canonical s)
    calc
      canonical s ≤ act (plus t r) s := canonical_le s (plus t r)
      _ = act t (canonical s) := by rw [hr, act_plus]
      _ = canonical (canonical s) := ht.symm

def minRotation (x : BitVec 39) : BitVec 39 :=
  pickMin x ((List.finRange 39).map (rotate · x))

theorem minRotation_member (x : BitVec 39) : ∃ r, minRotation x = rotate r x := by
  rcases List.mem_cons.mp (pickMin_spec x ((List.finRange 39).map (rotate · x))).1 with h | h
  · exact ⟨0, h.trans (rotate_zero x).symm⟩
  · obtain ⟨r, _, hr⟩ := List.mem_map.mp h
    exact ⟨r, hr.symm⟩

theorem minRotation_le (x : BitVec 39) (r : Shift) : minRotation x ≤ rotate r x :=
  (pickMin_spec x ((List.finRange 39).map (rotate · x))).2 _
    (List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨r, by simp, rfl⟩)))

theorem minRotation_le_rotated (r : Shift) (x : BitVec 39) :
    minRotation x ≤ minRotation (rotate r x) := by
  obtain ⟨t, ht⟩ := minRotation_member (rotate r x)
  rw [ht, rotate_plus]
  exact minRotation_le x (plus t r)

theorem minRotation_invariant (r : Shift) (x : BitVec 39) :
    minRotation (rotate r x) = minRotation x := by
  apply Std.le_antisymm
  · have h := minRotation_le_rotated (neg r) (rotate r x)
    rw [rotate_neg] at h
    exact h
  · exact minRotation_le_rotated r x

def syndrome (column : Coord → BitVec 39) : List Coord → BitVec 39
  | [] => 0
  | q :: qs => column q ^^^ syndrome column qs

theorem syndrome_perm (column : Coord → BitVec 39) {a b : List Coord}
    (h : a.Perm b) : syndrome column a = syndrome column b := by
  induction h with
  | nil => rfl
  | cons q _ ih => simp only [syndrome, ih]
  | swap q r xs =>
      simp only [syndrome]
      rw [← BitVec.xor_assoc, BitVec.xor_comm (column r) (column q), BitVec.xor_assoc]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def Equivariant (column : Coord → BitVec 39) : Prop :=
  ∀ r q, column (shift r q) = rotate r (column q)

/-- One checked generator suffices for the whole cyclic action. -/
theorem equivariant_of_generator (column : Coord → BitVec 39)
    (one : ∀ q, column (shift 1 q) = rotate 1 (column q)) : Equivariant column := by
  have all : ∀ n (hn : n < 39) q,
      column (shift ⟨n, hn⟩ q) = rotate ⟨n, hn⟩ (column q) := by
    intro n
    induction n with
    | zero => intro hn q; exact (congrArg column (shift_zero q)).trans (rotate_zero _).symm
    | succ n ih =>
      intro hn q
      have hn' : n < 39 := by omega
      have hp : plus 1 ⟨n, hn'⟩ = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        change (1 + n) % 39 = n + 1
        omega
      rw [← hp, ← shift_plus, one, ih hn', rotate_plus]
  intro r q
  exact all r.val r.isLt q

theorem syndrome_map (column : Coord → BitVec 39) (h : Equivariant column)
    (r : Shift) (xs : List Coord) :
    syndrome column (xs.map (shift r)) = rotate r (syndrome column xs) := by
  induction xs with
  | nil => exact (rotate_empty r).symm
  | cons q qs ih => simp only [List.map_cons, syndrome, h r q, ih, rotate_xor]

theorem syndrome_act (column : Coord → BitVec 39) (h : Equivariant column)
    (r : Shift) (s : Support) :
    syndrome column (act r s).val = rotate r (syndrome column s.val) := by
  exact (syndrome_perm column (sortSupport_perm _)).trans (syndrome_map column h r s.val)

theorem syndrome_ofNat (column : Coord → Nat) (xs : List Coord) :
    syndrome (fun q => BitVec.ofNat 39 (column q)) xs =
      BitVec.ofNat 39 (QEC663.Architecture.supportSyndrome column xs) := by
  induction xs with
  | nil => rfl
  | cons q qs ih => simp only [syndrome, QEC663.Architecture.supportSyndrome, ih, BitVec.ofNat_xor]

end QEC663.Orbit
