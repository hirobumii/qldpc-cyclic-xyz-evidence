import QLDPC.Rank

namespace QLDPC

@[simp] theorem pauli_zero_add (p : Pauli n) : Pauli.zero.add p = p := by
  cases p
  simp [Pauli.add, Pauli.zero]

@[simp] theorem pauli_add_zero (p : Pauli n) : p.add Pauli.zero = p := by
  cases p
  simp [Pauli.add, Pauli.zero]

@[simp] theorem pauli_add_self (p : Pauli n) : p.add p = Pauli.zero := by
  simp [Pauli.add, Pauli.zero]

theorem pauli_add_shuffle (a b c d : Pauli n) :
    (a.add b).add (c.add d) = (a.add c).add (b.add d) := by
  simp only [Pauli.add, Pauli.mk.injEq]
  constructor
  · rw [BitVec.xor_assoc, ← BitVec.xor_assoc b.x c.x d.x, BitVec.xor_comm b.x c.x, BitVec.xor_assoc, BitVec.xor_assoc]
  · rw [BitVec.xor_assoc, ← BitVec.xor_assoc b.z c.z d.z, BitVec.xor_comm b.z c.z, BitVec.xor_assoc, BitVec.xor_assoc]

@[simp] theorem linComb_zero (B : Fin r → Pauli n) :
    linComb B (fun _ => false) = Pauli.zero := by
  induction r with
  | zero => rfl
  | succ r ih => simp [linComb, ih]

theorem linComb_add (B : Fin r → Pauli n) (c d : Fin r → Bool) :
    linComb B (fun i => c i ^^ d i) = (linComb B c).add (linComb B d) := by
  induction r with
  | zero => simp [linComb]
  | succ r ih =>
    simp only [linComb]
    rw [ih]
    rw [pauli_add_shuffle]
    have hhead : ∀ a b : Bool, (if a ^^ b then B 0 else Pauli.zero) =
        (if a then B 0 else Pauli.zero).add (if b then B 0 else Pauli.zero) := by
      intro a b
      cases a <;> cases b <;> simp
    rw [hhead]

@[simp] theorem linComb_single (B : Fin r → Pauli n) (j : Fin r) :
    linComb B (fun i => decide (i = j)) = B j := by
  induction r with
  | zero => exact Fin.elim0 j
  | succ r ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [linComb, Fin.succ_ne_zero]
    · simp only [linComb, (Ne.symm (Fin.succ_ne_zero k)), decide_false,
        Bool.false_eq_true, ↓reduceIte, Fin.succ_inj]
      rw [ih]
      exact pauli_zero_add _

/-- Membership is equivalent to an actual finite coefficient expansion. -/
theorem span_iff_coefficients (B : Fin r → Pauli n) (p : Pauli n) :
    InSpan (List.ofFn B) p ↔ ∃ c, linComb B c = p := by
  constructor
  · intro h
    induction h with
    | zero => exact ⟨fun _ => false, linComb_zero B⟩
    | of_mem hm =>
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hm
      exact ⟨fun i => decide (i = j), linComb_single B j⟩
    | add _ _ ih1 ih2 =>
      obtain ⟨c, hc⟩ := ih1
      obtain ⟨d, hd⟩ := ih2
      exact ⟨fun i => c i ^^ d i, by rw [linComb_add, hc, hd]⟩
  · rintro ⟨c, rfl⟩
    apply linComb_inSpan
    intro i
    exact InSpan.of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- The basis certificate supplies unique binary coordinates for every span vector. -/
theorem binaryBasis_unique_coordinates (h : IsBinaryBasis S B) :
    ∀ p, InSpan S p → ∃ c, linComb B c = p ∧ ∀ d, linComb B d = p → d = c := by
  intro p hp
  obtain ⟨c, hc⟩ := (span_iff_coefficients B p).mp ((h.1 p).mp hp)
  refine ⟨c, hc, ?_⟩
  intro d hd
  have hz : linComb B (fun i => d i ^^ c i) = Pauli.zero := by
    rw [linComb_add, hd, hc, pauli_add_self]
  have heq := h.2 _ hz
  funext i
  have hi := heq i
  cases hdi : d i <;> cases hci : c i <;> simp_all

end QLDPC
