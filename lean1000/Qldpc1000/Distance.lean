import Qldpc1000.Lower
import Qldpc1000.CommutationConcrete

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Qldpc1000

/-- Literal PR3863 weight-six logical representatives. -/
def xWitness : Vec 1000 := ofSupport Data.witnessX
def zWitness : Vec 1000 := ofSupport Data.witnessZ
def xSeparator : Vec 1000 := ofSupport Data.separatorX
def zSeparator : Vec 1000 := ofSupport Data.separatorZ

theorem css_commutes : ∀ xr ∈ stored false, ∀ zr ∈ stored true,
    dot (ofSupport xr : Vec 1000) (ofSupport zr) = false :=
  Commutation.literal_css_commutes

theorem x_witness_kernel : Kernel (stored true) xWitness :=
  kernelCheck_sound _ _ (by decide)
theorem z_witness_kernel : Kernel (stored false) zWitness :=
  kernelCheck_sound _ _ (by decide)
theorem x_separator_kernel : Kernel (stored false) xSeparator :=
  kernelCheck_sound _ _ (by decide)
theorem z_separator_kernel : Kernel (stored true) zSeparator :=
  kernelCheck_sound _ _ (by decide)

theorem x_witness_weight : weight xWitness = 6 := by decide
theorem z_witness_weight : weight zWitness = 6 := by decide
theorem x_pairing : dot xWitness xSeparator = true := by decide
theorem z_pairing : dot zWitness zSeparator = true := by decide

theorem x_logical : Logical (stored true) (stored false) xWitness :=
  ⟨x_witness_kernel, not_span_of_separator x_separator_kernel x_pairing⟩
theorem z_logical : Logical (stored false) (stored true) zWitness :=
  ⟨z_witness_kernel, not_span_of_separator z_separator_kernel z_pairing⟩

theorem logical_nonzero {opposite same : List (List Nat)} {v : Vec n}
    (h : Logical opposite same v) : v ≠ zero := by
  intro hz
  rw [hz] at h
  exact h.2 RowSpan.zero

theorem x_lower (v : Vec 1000) (h : Logical (stored true) (stored false) v) :
    6 ≤ weight v := literal_kernel_minimum true v (logical_nonzero h) h.1
theorem z_lower (v : Vec 1000) (h : Logical (stored false) (stored true) v) :
    6 ≤ weight v := literal_kernel_minimum false v (logical_nonzero h) h.1

/-- Physical Pauli support counts a site once when either binary component
is nonzero. In particular Y has weight one, not two. -/
def pauliWeight (x z : Vec n) : Nat := weight (fun q => x q || z q)

/-- CSS normalizer modulo the genuine X/Z stabilizer row spaces. Phases are
quotiented out, as in the binary CSS distance convention. -/
def PauliLogical (x z : Vec 1000) : Prop :=
  Kernel (stored true) x ∧ Kernel (stored false) z ∧
    ¬ (RowSpan (stored false) x ∧ RowSpan (stored true) z)

theorem filter_length_mono (p q : α → Bool) (s : List α)
    (h : ∀ a, p a = true → q a = true) : (s.filter p).length ≤ (s.filter q).length := by
  induction s with
  | nil => exact Nat.le_refl 0
  | cons a s ih =>
    by_cases hp : p a = true
    · have hq := h a hp
      simpa [hp, hq] using Nat.succ_le_succ ih
    · have hf : p a = false := Bool.eq_false_iff.mpr hp
      cases hq : q a <;> simp [hf, hq] <;> omega

theorem x_weight_le_pauli (x z : Vec n) : weight x ≤ pauliWeight x z := by
  apply filter_length_mono
  intro a ha
  simp [ha]
theorem z_weight_le_pauli (x z : Vec n) : weight z ≤ pauliWeight x z := by
  apply filter_length_mono
  intro a ha
  simp [ha]

theorem pauli_lower (x z : Vec 1000) (h : PauliLogical x z) : 6 ≤ pauliWeight x z := by
  by_cases hx : x = zero
  · have hz : z ≠ zero := by
      intro hz
      apply h.2.2
      rw [hx, hz]
      exact ⟨RowSpan.zero, RowSpan.zero⟩
    exact Nat.le_trans (literal_kernel_minimum false z hz h.2.1) (z_weight_le_pauli x z)
  · exact Nat.le_trans (literal_kernel_minimum true x hx h.1) (x_weight_le_pauli x z)

theorem zero_kernel (rows : List (List Nat)) : Kernel rows (zero : Vec n) := by
  intro row _
  exact dot_zero_right _

theorem x_pauli_logical : PauliLogical xWitness zero :=
  ⟨x_witness_kernel, zero_kernel _, fun h => x_logical.2 h.1⟩
theorem x_pauli_weight : pauliWeight xWitness zero = 6 := by
  simpa [pauliWeight, zero] using x_witness_weight

theorem x_exists_distance : ∃ d, DistanceAtMost (n := 1000) (stored true) (stored false) d :=
  ⟨6, xWitness, x_logical, by simp [x_witness_weight]⟩
theorem z_exists_distance : ∃ d, DistanceAtMost (n := 1000) (stored false) (stored true) d :=
  ⟨6, zWitness, z_logical, by simp [z_witness_weight]⟩

def PauliDistanceAtMost (d : Nat) : Prop :=
  ∃ x z, PauliLogical x z ∧ pauliWeight x z ≤ d
theorem pauli_exists_distance : ∃ d, PauliDistanceAtMost d :=
  ⟨6, xWitness, zero, x_pauli_logical, by simp [x_pauli_weight]⟩

/-- Well-ordering supplies a genuine minimum; the numeral six is not built
into the definition of any distance. -/
theorem exists_least (P : Nat → Prop) (hex : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, P m → n ≤ m := by
  classical
  obtain ⟨n, hn⟩ := hex
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases smaller : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hp⟩ := smaller
      exact ih m hm hp
    · refine ⟨n, hn, ?_⟩
      intro m hm
      by_cases hnm : n ≤ m
      · exact hnm
      · exact False.elim (smaller ⟨m, by omega, hm⟩)

noncomputable def leastNat (P : Nat → Prop) (hex : ∃ n, P n) : Nat :=
  Classical.choose (exists_least P hex)
theorem leastNat_spec (P : Nat → Prop) (hex : ∃ n, P n) :
    P (leastNat P hex) ∧ ∀ m, P m → leastNat P hex ≤ m :=
  Classical.choose_spec (exists_least P hex)

noncomputable def dX : Nat := leastNat _ x_exists_distance
noncomputable def dZ : Nat := leastNat _ z_exists_distance
noncomputable def d : Nat := leastNat _ pauli_exists_distance

theorem dX_eq_six : dX = 6 := by
  classical
  have upper : dX ≤ 6 := (leastNat_spec _ x_exists_distance).2 6
    ⟨xWitness, x_logical, by simp [x_witness_weight]⟩
  obtain ⟨v, hv, hw⟩ := (leastNat_spec _ x_exists_distance).1
  have lower := x_lower v hv
  change weight v ≤ dX at hw
  omega

theorem dZ_eq_six : dZ = 6 := by
  classical
  have upper : dZ ≤ 6 := (leastNat_spec _ z_exists_distance).2 6
    ⟨zWitness, z_logical, by simp [z_witness_weight]⟩
  obtain ⟨v, hv, hw⟩ := (leastNat_spec _ z_exists_distance).1
  have lower := z_lower v hv
  change weight v ≤ dZ at hw
  omega

theorem d_eq_six : d = 6 := by
  classical
  have upper : d ≤ 6 := (leastNat_spec _ pauli_exists_distance).2 6
    ⟨xWitness, zero, x_pauli_logical, by simp [x_pauli_weight]⟩
  obtain ⟨x, z, h, hw⟩ := (leastNat_spec _ pauli_exists_distance).1
  have lower := pauli_lower x z h
  change pauliWeight x z ≤ d at hw
  omega

/-- Unconditional exact distances of the literal published CSS matrices. -/
theorem exact_distance : dX = 6 ∧ dZ = 6 ∧ d = 6 := ⟨dX_eq_six, dZ_eq_six, d_eq_six⟩


end Qldpc1000
