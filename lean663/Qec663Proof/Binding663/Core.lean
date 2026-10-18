import Std

namespace Binding663

/-- A genuine vector in the finite binary coordinate space. -/
abbrev Vec (n : Nat) := Fin n → Bool

def zero : Vec n := fun _ => false
def add (u v : Vec n) : Vec n := fun i => u i ^^ v i

/-- Standard finite binary inner product, over all coordinates. -/
def dot : {n : Nat} → Vec n → Vec n → Bool
  | 0, _, _ => false
  | n + 1, u, v =>
      (u ⟨0, Nat.zero_lt_succ n⟩ && v ⟨0, Nat.zero_lt_succ n⟩) ^^
      dot (fun i : Fin n => u i.succ) (fun i : Fin n => v i.succ)

private theorem bool_distrib (a b c d e : Bool) :
    ((a && (b ^^ c)) ^^ (d ^^ e)) =
      (((a && b) ^^ d) ^^ ((a && c) ^^ e)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem dot_comm (u v : Vec n) : dot u v = dot v u := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [dot]
      rw [ih, Bool.and_comm]

theorem dot_zero_right (u : Vec n) : dot u zero = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((u ⟨0, Nat.zero_lt_succ n⟩ && false) ^^
        dot (fun i : Fin n => u i.succ) zero) = false
      rw [ih]
      simp

theorem dot_zero_left (u : Vec n) : dot zero u = false := by
  rw [dot_comm, dot_zero_right]

theorem dot_add_right (u v w : Vec n) :
    dot u (add v w) = (dot u v ^^ dot u w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((u ⟨0, Nat.zero_lt_succ n⟩ &&
          (v ⟨0, Nat.zero_lt_succ n⟩ ^^ w ⟨0, Nat.zero_lt_succ n⟩)) ^^
          dot (fun i : Fin n => u i.succ)
            (add (fun i : Fin n => v i.succ) (fun i : Fin n => w i.succ))) =
        (((u ⟨0, Nat.zero_lt_succ n⟩ && v ⟨0, Nat.zero_lt_succ n⟩) ^^
          dot (fun i : Fin n => u i.succ) (fun i : Fin n => v i.succ)) ^^
         ((u ⟨0, Nat.zero_lt_succ n⟩ && w ⟨0, Nat.zero_lt_succ n⟩) ^^
          dot (fun i : Fin n => u i.succ) (fun i : Fin n => w i.succ)))
      rw [ih]
      exact bool_distrib _ _ _ _ _

theorem dot_add_left (u v w : Vec n) :
    dot (add u v) w = (dot u w ^^ dot v w) := by
  rw [dot_comm, dot_add_right, dot_comm w u, dot_comm w v]

/-- Coordinates outside the ambient vector are zero. -/
def eval (v : Vec n) (i : Nat) : Bool :=
  if h : i < n then v ⟨i, h⟩ else false

/-- A single standard basis vector; outside coordinates contribute zero. -/
def oneHot (i : Nat) : Vec n := fun j => decide (j.val = i)

private theorem oneHot_tail_zero :
    (fun j : Fin n => (oneHot 0 : Vec (n + 1)) j.succ) = zero := by
  funext j
  simp [oneHot, zero]

private theorem oneHot_tail_succ (i : Nat) :
    (fun j : Fin n => (oneHot (i + 1) : Vec (n + 1)) j.succ) = oneHot i := by
  funext j
  simp [oneHot]

theorem dot_oneHot (i : Nat) (v : Vec n) : dot (oneHot i) v = eval v i := by
  induction n generalizing i with
  | zero => simp [dot, eval]
  | succ n ih =>
      cases i with
      | zero =>
          simp only [dot]
          rw [oneHot_tail_zero, dot_zero_left]
          simp [oneHot, eval]
      | succ i =>
          simp only [dot]
          rw [oneHot_tail_succ, ih]
          simp [oneHot, eval, Nat.succ_lt_succ_iff]

/-- Encode the literal sparse row as its F₂ sum of standard basis vectors.
Duplicate coordinates cancel, exactly as binary matrix arithmetic requires. -/
def ofSupport : List Nat → Vec n
  | [] => zero
  | i :: is => add (oneHot i) (ofSupport is)

/-- Transparent sparse evaluation of a binary row on a finite vector. -/
def sparseParity : List Nat → Vec n → Bool
  | [], _ => false
  | i :: is, v => eval v i ^^ sparseParity is v

theorem dot_ofSupport (s : List Nat) (v : Vec n) :
    dot (ofSupport s) v = sparseParity s v := by
  induction s with
  | nil => exact dot_zero_left v
  | cons i is ih => simp only [ofSupport, sparseParity, dot_add_left, dot_oneHot, ih]

/-- The actual matrix kernel, using the full finite inner product. -/
def Kernel (rows : List (List Nat)) (v : Vec n) : Prop :=
  ∀ row ∈ rows, dot (ofSupport row) v = false

/-- The genuine F₂ linear span of the literal rows. -/
inductive RowSpan (rows : List (List Nat)) : Vec n → Prop where
  | zero : RowSpan rows zero
  | row {s : List Nat} : s ∈ rows → RowSpan rows (ofSupport s)
  | add {u v : Vec n} : RowSpan rows u → RowSpan rows v → RowSpan rows (add u v)

/-- Boolean computation is linked to the true matrix kernel by a proved identity. -/
def kernelCheck (rows : List (List Nat)) (v : Vec n) : Bool :=
  rows.all (fun row => !(sparseParity row v))

theorem kernelCheck_sound (rows : List (List Nat)) (v : Vec n)
    (h : kernelCheck rows v = true) : Kernel rows v := by
  intro row hr
  rw [dot_ofSupport]
  have hp := List.all_eq_true.mp h row hr
  cases hs : sparseParity row v <;> simp_all

/-- A dual vector vanishing on every row vanishes on every F₂ combination. -/
theorem span_annihilated {rows : List (List Nat)} {f v : Vec n}
    (hf : Kernel rows f) (hv : RowSpan rows v) : dot v f = false := by
  induction hv with
  | zero => exact dot_zero_left f
  | row hr => exact hf _ hr
  | add _ _ ihu ihv => simp [dot_add_left, ihu, ihv]

theorem not_span_of_separator {rows : List (List Nat)} {f v : Vec n}
    (hf : Kernel rows f) (h : dot v f = true) : ¬ RowSpan rows v := by
  intro hv
  have hn := span_annihilated hf hv
  rw [h] at hn
  cases hn

/-- Ordinary Hamming weight on all n coordinates. -/
def weight (v : Vec n) : Nat :=
  ((List.finRange n).filter fun i => v i).length

/-- A CSS X-sector logical vector, with checks and stabilizers supplied separately. -/
def Logical (opposite same : List (List Nat)) (v : Vec n) : Prop :=
  Kernel opposite v ∧ ¬ RowSpan same v

def DistanceAtMost {n : Nat} (opposite same : List (List Nat)) (d : Nat) : Prop :=
  ∃ v : Vec n, Logical opposite same v ∧ weight v ≤ d

end Binding663
