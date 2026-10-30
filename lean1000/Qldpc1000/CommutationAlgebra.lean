import Qldpc1000.Core

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Qldpc1000.Commutation

def vvIndex (k j : Fin 3) (u : Fin 100) : Nat := 100 * (3*k.val+j.val)+u.val
def ccIndex (u : Fin 100) : Nat := 900+u.val

@[simp] theorem vvIndex_lt (k j : Fin 3) (u : Fin 100) : vvIndex k j u < 1000 := by
  have := k.isLt; have := j.isLt; have := u.isLt
  unfold vvIndex
  omega
@[simp] theorem ccIndex_lt (u : Fin 100) : ccIndex u < 1000 := by
  have := u.isLt
  unfold ccIndex
  omega

@[simp] theorem vvIndex_eq (k j l m : Fin 3) (u v : Fin 100) :
    vvIndex k j u = vvIndex l m v ↔ k = l ∧ j = m ∧ u = v := by
  have := k.isLt; have := j.isLt; have := l.isLt; have := m.isLt
  have := u.isLt; have := v.isLt
  simp only [vvIndex, Fin.ext_iff]
  omega
@[simp] theorem ccIndex_eq (u v : Fin 100) : ccIndex u = ccIndex v ↔ u = v := by
  simp [ccIndex, Fin.ext_iff]
@[simp] theorem vv_ne_cc (k j : Fin 3) (u v : Fin 100) : vvIndex k j u ≠ ccIndex v := by
  have := k.isLt; have := j.isLt; have := u.isLt
  unfold vvIndex ccIndex
  omega
@[simp] theorem cc_ne_vv (k j : Fin 3) (u v : Fin 100) : ccIndex u ≠ vvIndex k j v :=
  Ne.symm (vv_ne_cc k j v u)

/-- X(j,t): A_k=I+L_k on VV(k,j), B_j=I+R_j on CC. -/
def xRow (L R : Fin 3 → Fin 100 → Fin 100) (j : Fin 3) (t : Fin 100) : List Nat :=
  [vvIndex 0 j t, vvIndex 0 j (L 0 t),
   vvIndex 1 j t, vvIndex 1 j (L 1 t),
   vvIndex 2 j t, vvIndex 2 j (L 2 t), ccIndex t, ccIndex (R j t)]

/-- Z(k,s): B_j^T on VV(k,j), A_k^T on CC. The inverse actions
are essential: this is the transpose convention of the published code. -/
def zRow (Li Ri : Fin 3 → Fin 100 → Fin 100) (k : Fin 3) (s : Fin 100) : List Nat :=
  [vvIndex k 0 s, vvIndex k 0 (Ri 0 s),
   vvIndex k 1 s, vvIndex k 1 (Ri 1 s),
   vvIndex k 2 s, vvIndex k 2 (Ri 2 s), ccIndex s, ccIndex (Li k s)]

theorem inverse_eq_iff {α : Type} (f g : α → α)
    (fg : ∀ x, f (g x) = x) (gf : ∀ x, g (f x) = x) (x y : α) :
    x = g y ↔ f x = y := by
  constructor
  · intro h; rw [h, fg]
  · intro h
    have hh := congrArg g h
    rw [gf] at hh
    exact hh

/-- The four overlap terms from VV and CC cancel in pairs. This is
A_k B_j + B_j A_k = 0 over F2, for arbitrary commuting bijections. -/
theorem overlap_cancels {α : Type} [DecidableEq α]
    (L R Li Ri : α → α)
    (LLi : ∀ x, L (Li x) = x) (LiL : ∀ x, Li (L x) = x)
    (RRi : ∀ x, R (Ri x) = x) (RiR : ∀ x, Ri (R x) = x)
    (commute : ∀ x, R (L x) = L (R x)) (t s : α) :
    ((decide (t = s) ^^ (decide (t = Ri s) ^^
      (decide (L t = s) ^^ decide (L t = Ri s)))) ^^
    (decide (t = s) ^^ (decide (t = Li s) ^^
      (decide (R t = s) ^^ decide (R t = Li s))))) = false := by
  have h1 : (t = Ri s) = (R t = s) := propext (inverse_eq_iff R Ri RRi RiR t s)
  have h2 : (t = Li s) = (L t = s) := propext (inverse_eq_iff L Li LLi LiL t s)
  have h3 : (L t = Ri s) = (R t = Li s) := by
    apply propext
    rw [inverse_eq_iff R Ri RRi RiR, commute, ← inverse_eq_iff L Li LLi LiL]
  simp only [h1, h2, h3]
  generalize decide (t = s) = a
  generalize decide (R t = s) = b
  generalize decide (L t = s) = c
  generalize decide (R t = Li s) = d
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem fin3_cases (q : Fin 3) : q = 0 ∨ q = 1 ∨ q = 2 := by
  have := q.isLt
  have h : q.val = 0 ∨ q.val = 1 ∨ q.val = 2 := by omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-- The product proof is independent of the concrete group and input data.
Different VV blocks and VV/CC coordinates are disjoint; the only two
overlaps contribute A_k B_j and B_j A_k respectively. -/
theorem product_rows_commute (L R Li Ri : Fin 3 → Fin 100 → Fin 100)
    (LLi : ∀ k x, L k (Li k x) = x) (LiL : ∀ k x, Li k (L k x) = x)
    (RRi : ∀ j x, R j (Ri j x) = x) (RiR : ∀ j x, Ri j (R j x) = x)
    (commute : ∀ k j x, R j (L k x) = L k (R j x))
    (j k : Fin 3) (t s : Fin 100) :
    dot (ofSupport (xRow L R j t) : Vec 1000) (ofSupport (zRow Li Ri k s)) = false := by
  have hc := overlap_cancels (L k) (R j) (Li k) (Ri j)
    (LLi k) (LiL k) (RRi j) (RiR j) (commute k j) t s
  rcases fin3_cases j with rfl | rfl | rfl <;>
    rcases fin3_cases k with rfl | rfl | rfl <;>
    rw [dot_ofSupport] <;>
    simpa [xRow, zRow, sparseParity, eval, ofSupport,
      add, zero, oneHot, Bool.xor_assoc] using hc

theorem ofSupport_perm {s t : List Nat} (h : s.Perm t) :
    (ofSupport s : Vec n) = ofSupport t := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [ofSupport, ih]
  | swap a b s =>
    funext q
    simp only [ofSupport, add]
    exact Bool.xor_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Qldpc1000.Commutation
