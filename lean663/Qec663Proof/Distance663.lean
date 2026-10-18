import Qec663Proof.ActualVectorLower
import Qec663Proof.ConcreteLowerBound
import Qec663Proof.ConcreteParity
import Qec663Proof.Binding663.CommutationActual

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Exact distance for the literal 663-coordinate binary CSS object.
The lower bounds below have no mathematical hypotheses. The finite native
checks and their compiler/runtime trust are visible in `#print axioms`.
This file does not assert a rank theorem, Hilbert-space phase semantics,
decoder performance, or an official leaderboard certification status.
-/
namespace Qec663
open Binding663 QEC663.Architecture Qec663.Structure Qec663.Integration

theorem x_kernel_min10 (v : Vec 663) (h : Kernel hz v) (hne : v ≠ zero) :
    10 ≤ weight v :=
  x_physical_lower_bound actual_x_classical_zero_or_lower x_augmentation v h hne

theorem z_kernel_min10 (v : Vec 663) (h : Kernel hx v) (hne : v ≠ zero) :
    10 ≤ weight v :=
  z_physical_lower_bound actual_z_classical_zero_or_lower z_augmentation v h hne

def HasSectorDistance (opposite same : List (List Nat)) (d : Nat) : Prop :=
  (∀ v : Vec 663, Logical opposite same v → d ≤ weight v) ∧
  (∃ v : Vec 663, Logical opposite same v ∧ weight v = d)

theorem code663_dX_exact : HasSectorDistance hz hx 10 := by
  constructor
  · intro v hv
    apply x_kernel_min10 v hv.1
    intro h
    exact hv.2 (h ▸ RowSpan.zero)
  · exact ⟨xWitness, x_logical, x_weight⟩

theorem code663_dZ_exact : HasSectorDistance hx hz 10 := by
  constructor
  · intro v hv
    apply z_kernel_min10 v hv.1
    intro h
    exact hv.2 (h ▸ RowSpan.zero)
  · exact ⟨zWitness, z_logical, z_weight⟩

/-- A phase-free Pauli as its two genuine binary coordinate vectors. -/
structure Pauli where
  x : Vec 663
  z : Vec 663

def Pauli.weight (p : Pauli) : Nat := Binding663.weight (fun i => p.x i || p.z i)

def Pauli.Logical (p : Pauli) : Prop :=
  Kernel hz p.x ∧ Kernel hx p.z ∧ ¬ (RowSpan hx p.x ∧ RowSpan hz p.z)

private theorem filter_length_mono (l : List α) (p q : α → Bool)
    (h : ∀ a, p a = true → q a = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    have hh := h a
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

theorem Pauli.x_weight_le (p : Pauli) : Binding663.weight p.x ≤ p.weight := by
  apply filter_length_mono
  intro i h
  simp [h]

theorem Pauli.z_weight_le (p : Pauli) : Binding663.weight p.z ≤ p.weight := by
  apply filter_length_mono
  intro i h
  simp [h]

/-- The Pauli statement includes mixed X/Z errors and uses union support weight. -/
theorem code663_pauli_lower (p : Pauli) (hp : p.Logical) : 10 ≤ p.weight := by
  by_cases hxzero : p.x = zero
  · have hznonzero : p.z ≠ zero := by
      intro hzzero
      apply hp.2.2
      constructor
      · rw [hxzero]; exact RowSpan.zero
      · rw [hzzero]; exact RowSpan.zero
    exact Nat.le_trans (z_kernel_min10 p.z hp.2.1 hznonzero) p.z_weight_le
  · exact Nat.le_trans (x_kernel_min10 p.x hp.1 hxzero) p.x_weight_le

def HasPauliDistance (d : Nat) : Prop :=
  (∀ p : Pauli, p.Logical → d ≤ p.weight) ∧
  (∃ p : Pauli, p.Logical ∧ p.weight = d)

/-- Exact phase-free binary Pauli distance of the literal CSS check pair. -/
theorem code663_distance_exact : HasPauliDistance 10 := by
  constructor
  · exact code663_pauli_lower
  · refine ⟨⟨xWitness, zero⟩, ?_, ?_⟩
    · refine ⟨x_kernel, ?_, ?_⟩
      · intro row _
        exact dot_zero_right _
      · intro h
        exact x_not_rowSpan h.1
    · simpa [Pauli.weight, zero] using x_weight

/-- Actual CSS commutation and both sector distances, together with the
mixed-Pauli statement. Row ranks and Hilbert-space phases are separate. -/
theorem code663_css_distance_certificate :
    (∀ x ∈ hx, Kernel hz (ofSupport (n := 663) x)) ∧
    HasSectorDistance hz hx 10 ∧ HasSectorDistance hx hz 10 ∧ HasPauliDistance 10 :=
  ⟨hx_rows_kernel_hz, code663_dX_exact, code663_dZ_exact, code663_distance_exact⟩

#print axioms x_kernel_min10
#print axioms z_kernel_min10
#print axioms code663_dX_exact
#print axioms code663_dZ_exact
#print axioms code663_distance_exact
#print axioms code663_css_distance_certificate
end Qec663
