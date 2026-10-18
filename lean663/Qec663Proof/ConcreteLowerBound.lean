import Qec663Proof.Binding663.Bridge
import Qec663Proof.SliceArithmetic
import Qec663Proof.ConcreteSingletonExclusion

namespace Qec663.Structure
open Binding663

/-- The literal physical X-kernel lower bound after the explicitly named
classical and augmentation interfaces are discharged. -/
theorem x_physical_lower_bound
    (classicalLower : ∀ v : Vec 156, xSyndrome v = zero → weight v = 0 ∨ 10 ≤ weight v)
    (augmentation : ∀ (i : Fin 4) (v : Vec 156) (c : Vec 39),
      xSyndrome v = xTarget i c → weight v % 2 = weight c % 2)
    (v : Vec 663) (hkernel : Kernel hz v) (hne : v ≠ zero) : 10 ≤ weight v := by
  let w : FourSliceWord (Vec 156) (Vec 39) := ⟨xSlice v, ccPart v⟩
  have hw : w.weight weight weight = weight v := (x_weight_partition v).symm
  rw [← hw]
  apply four_slice_cycle_lower_bound_of_singletons zero weight weight xSyndrome xTarget
    (fun p : Fin 156 => xSyndrome (oneHot p.val)) (w := w)
  · exact weight_zero_iff
  · intro u hu
    rw [(weight_zero_iff u).mp hu]
    exact (syndromeLinear bSupports true).map_zero
  · exact x_target_zero
  · exact x_target_nonzero
  · exact classicalLower
  · exact augmentation
  · exact syndrome_singleton_column bSupports true
  · exact x_target_singletons_excluded
  · exact x_kernel_slice_equation v hkernel
  · rw [hw]
    have hpos : weight v ≠ 0 := by
      intro h
      exact hne ((weight_zero_iff v).mp h)
    omega

/-- The literal physical Z-kernel lower bound, with the same explicit interfaces. -/
theorem z_physical_lower_bound
    (classicalLower : ∀ v : Vec 156, zSyndrome v = zero → weight v = 0 ∨ 10 ≤ weight v)
    (augmentation : ∀ (i : Fin 4) (v : Vec 156) (c : Vec 39),
      zSyndrome v = zTarget i c → weight v % 2 = weight c % 2)
    (v : Vec 663) (hkernel : Kernel hx v) (hne : v ≠ zero) : 10 ≤ weight v := by
  let w : FourSliceWord (Vec 156) (Vec 39) := ⟨zSlice v, ccPart v⟩
  have hw : w.weight weight weight = weight v := (z_weight_partition v).symm
  rw [← hw]
  apply four_slice_cycle_lower_bound_of_singletons zero weight weight zSyndrome zTarget
    (fun p : Fin 156 => zSyndrome (oneHot p.val)) (w := w)
  · exact weight_zero_iff
  · intro u hu
    rw [(weight_zero_iff u).mp hu]
    exact (syndromeLinear aSupports false).map_zero
  · exact z_target_zero
  · exact z_target_nonzero
  · exact classicalLower
  · exact augmentation
  · exact syndrome_singleton_column aSupports false
  · exact z_target_singletons_excluded
  · exact z_kernel_slice_equation v hkernel
  · rw [hw]
    have hpos : weight v ≠ 0 := by
      intro h
      exact hne ((weight_zero_iff v).mp h)
    omega

#print axioms x_physical_lower_bound
#print axioms z_physical_lower_bound
end Qec663.Structure
