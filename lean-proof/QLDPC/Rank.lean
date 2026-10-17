import QLDPC.Basic

namespace QLDPC

/-- The binary coordinate numbered `j`: X coordinates followed by Z coordinates. -/
def coordinate (p : Pauli n) (j : Nat) : Bool :=
  if j < n then p.x.getLsbD j else p.z.getLsbD (j - n)

@[simp] theorem coordinate_zero (j : Nat) : coordinate (Pauli.zero : Pauli n) j = false := by
  simp [coordinate, Pauli.zero]

@[simp] theorem coordinate_add (p q : Pauli n) (j : Nat) :
    coordinate (p.add q) j = (coordinate p j ^^ coordinate q j) := by
  simp only [coordinate, Pauli.add, BitVec.getLsbD_xor]
  split <;> rfl

/-- Finite addition in F₂, with all coefficients retained in the logical statement. -/
def boolSum : {r : Nat} → (Fin r → Bool) → Bool
  | 0, _ => false
  | _ + 1, f => f 0 ^^ boolSum (fun i => f i.succ)

/-- A genuine binary linear combination of a finite vector family. -/
def linComb : {r : Nat} → (Fin r → Pauli n) → (Fin r → Bool) → Pauli n
  | 0, _, _ => Pauli.zero
  | _ + 1, B, c => (if c 0 then B 0 else Pauli.zero).add
      (linComb (fun i => B i.succ) (fun i => c i.succ))

@[simp] theorem boolSum_zero (r : Nat) : boolSum (fun _ : Fin r => false) = false := by
  induction r with
  | zero => rfl
  | succ r ih => simp [boolSum, ih]

@[simp] theorem boolSum_single (c : Fin r → Bool) (j : Fin r) :
    boolSum (fun i => c i && decide (i = j)) = c j := by
  induction r with
  | zero => exact Fin.elim0 j
  | succ r ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [boolSum, Fin.succ_ne_zero]
    · simp only [boolSum, (Ne.symm (Fin.succ_ne_zero k)), decide_false, Bool.and_false,
        Bool.false_xor, Fin.succ_inj]
      exact ih (fun i => c i.succ) k

 theorem coordinate_linComb (B : Fin r → Pauli n) (c : Fin r → Bool) (j : Nat) :
    coordinate (linComb B c) j = boolSum (fun i => c i && coordinate (B i) j) := by
  induction r with
  | zero => simp [linComb, boolSum]
  | succ r ih =>
    simp only [linComb, coordinate_add, boolSum]
    rw [ih]
    cases h : c 0 <;> simp [h]

 theorem linComb_inSpan (B : Fin r → Pauli n) (c : Fin r → Bool)
    (h : ∀ i, InSpan S (B i)) : InSpan S (linComb B c) := by
  induction r with
  | zero => exact InSpan.zero
  | succ r ih =>
    unfold linComb
    apply InSpan.add
    · split
      · exact h 0
      · exact InSpan.zero
    · exact ih _ _ (fun i => h i.succ)

 theorem span_mono_generators (h : ∀ p ∈ A, InSpan B p) :
    ∀ p, InSpan A p → InSpan B p := by
  intro p hp
  induction hp with
  | zero => exact InSpan.zero
  | of_mem hm => exact h _ hm
  | add _ _ ih1 ih2 => exact InSpan.add ih1 ih2

/-- A finite basis of the actual closure-defined binary row span.
The second clause rules out every nonzero binary coefficient relation. -/
def IsBinaryBasis (S : List (Pauli n)) (B : Fin r → Pauli n) : Prop :=
  (∀ p, InSpan S p ↔ InSpan (List.ofFn B) p) ∧
  (∀ c, linComb B c = Pauli.zero → ∀ i, c i = false)

/-- Semantic binary dimension, witnessed by a spanning independent family. -/
def HasBinaryDimension (S : List (Pauli n)) (r : Nat) : Prop :=
  ∃ B : Fin r → Pauli n, IsBinaryBasis S B

/-- A reduced pivot matrix recovers every coefficient, without enumerating coefficients. -/
theorem recover_coefficients (B : Fin r → Pauli n) (pivot : Fin r → Nat)
    (h : ∀ i j, coordinate (B i) (pivot j) = decide (i = j))
    (c : Fin r → Bool) (j : Fin r) :
    coordinate (linComb B c) (pivot j) = c j := by
  rw [coordinate_linComb]
  simp only [h]
  exact boolSum_single c j

 theorem independent_of_pivots (B : Fin r → Pauli n) (pivot : Fin r → Nat)
    (h : ∀ i j, coordinate (B i) (pivot j) = decide (i = j)) :
    ∀ c, linComb B c = Pauli.zero → ∀ i, c i = false := by
  intro c hc i
  have hr := recover_coefficients B pivot h c i
  rw [hc, coordinate_zero] at hr
  exact hr.symm

/-- A pair of finite change-of-generators certificates and an identity pivot
submatrix prove a basis of the original closure-defined row span. -/
theorem basis_of_certificates (G : Fin m → Pauli n) (B : Fin r → Pauli n)
    (S : List (Pauli n)) (source_binding : List.ofFn G = S)
    (fromSource : Fin r → Fin m → Bool) (toBasis : Fin m → Fin r → Bool)
    (hb : ∀ i, linComb G (fromSource i) = B i)
    (hg : ∀ i, linComb B (toBasis i) = G i)
    (pivot : Fin r → Nat)
    (hp : ∀ i j, coordinate (B i) (pivot j) = decide (i = j)) :
    IsBinaryBasis S B := by
  constructor
  · intro p
    constructor
    · apply span_mono_generators
      intro q hq
      rw [← source_binding] at hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      rw [← hg i]
      apply linComb_inSpan
      intro j
      exact InSpan.of_mem (List.mem_ofFn.mpr ⟨j, rfl⟩)
    · apply span_mono_generators
      intro q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      rw [← hb i]
      apply linComb_inSpan
      intro j
      apply InSpan.of_mem
      rw [← source_binding]
      exact List.mem_ofFn.mpr ⟨j, rfl⟩
  · exact independent_of_pivots B pivot hp

private theorem xor_shuffle (a b c d : Bool) :
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem xor_fold_linear (l : List α) (f g : α → Bool) (a b : Bool) :
    (l.map (fun i => f i ^^ g i)).foldl (· ^^ ·) (a ^^ b) =
      ((l.map f).foldl (· ^^ ·) a ^^ (l.map g).foldl (· ^^ ·) b) := by
  induction l generalizing a b with
  | nil => rfl
  | cons h t ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [xor_shuffle]
    exact ih _ _

private theorem xor_fold_zero (l : List α) :
    (l.map (fun _ => false)).foldl (· ^^ ·) false = false := by
  induction l with
  | nil => rfl
  | cons h t ih => simpa using ih

 theorem symplectic_zero_left (p : Pauli n) : Pauli.zero.symplectic p = false := by
  have hz : (Pauli.zero : Pauli n).localSymplectic p = (fun _ => false) := by
    funext i
    simp [Pauli.localSymplectic, Pauli.zero]
  simp only [Pauli.symplectic, hz]
  exact xor_fold_zero _

 theorem symplectic_add_left (p q t : Pauli n) :
    (p.add q).symplectic t = (p.symplectic t ^^ q.symplectic t) := by
  have hlocal : ∀ i, (p.add q).localSymplectic t i =
      (p.localSymplectic t i ^^ q.localSymplectic t i) := by
    intro i
    simp only [Pauli.localSymplectic, Pauli.add, BitVec.getLsbD_xor,
      Bool.and_xor_distrib_right]
    exact xor_shuffle _ _ _ _
  have hf := funext hlocal
  simp only [Pauli.symplectic, hf]
  exact xor_fold_linear _ _ _ false false

/-- Every vector in a binary span annihilates a common symplectic orthogonal. -/
theorem span_annihilator (t : Pauli n) (h : ∀ p ∈ S, Commutes p t) :
    ∀ p, InSpan S p → Commutes p t := by
  intro p hp
  induction hp with
  | zero => exact symplectic_zero_left t
  | of_mem hm => exact h _ hm
  | add _ _ ih1 ih2 =>
    unfold Commutes at *
    rw [symplectic_add_left, ih1, ih2]
    rfl

 theorem not_inSpan_of_anticommuting (t : Pauli n)
    (h : ∀ p ∈ S, Commutes p t) (hw : w.symplectic t = true) : ¬ InSpan S w := by
  intro hin
  have hzero := span_annihilator t h w hin
  unfold Commutes at hzero
  rw [hw] at hzero
  contradiction

end QLDPC
