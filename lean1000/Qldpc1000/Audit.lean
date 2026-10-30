import Qldpc1000.Distance

namespace Qldpc1000

/-- Includes matrix validity and the full/stored binding in the same audited
certificate as the three exact distances. Rank406 is not asserted here. -/
theorem certified_public_code :
    (∀ xr ∈ stored false, ∀ zr ∈ stored true,
      dot (ofSupport xr : Vec 1000) (ofSupport zr) = false) ∧
    (∀ z (v : Vec 1000), Kernel (fullRows z).toList v ↔ Kernel (stored z) v) ∧
    dX = 6 ∧ dZ = 6 ∧ d = 6 :=
  ⟨css_commutes, full_stored_kernel, dX_eq_six, dZ_eq_six, d_eq_six⟩

#print axioms bulk_transpose
#print axioms recipe_values
#print axioms local_cover
#print axioms LocalFormula.column_formula
#print axioms LocalFormula.neighbors_perm
#print axioms two_atoms
#print axioms four_atoms
#print axioms four_edges_impossible
#print axioms small_bipartite_impossible
#print axioms shore_syndromes_zero
#print axioms Cayley.difference_distinct
#print axioms Cayley.difference_injective
#print axioms Cayley.common_neighbors
#print axioms Cayley.signed_flips
#print axioms AlgebraicLocal.edge_simple
#print axioms AlgebraicLocal.no_rectangle
#print axioms AlgebraicLocal.formula_endpoints
#print axioms AlgebraicLocal.no_small
#print axioms AlgebraicLocal.shore_boundary_injective
#print axioms AlgebraicLocal.formula_nonedge
#print axioms designated_phase_separation
#print axioms nonedge_checked
#print axioms structural_lower
#print axioms syndrome_zero_of_vector_map_zero
#print axioms full_stored_kernel
#print axioms css_commutes
#print axioms Commutation.mul_assoc
#print axioms Commutation.product_rows_commute
#print axioms Commutation.stored_formula
#print axioms literal_kernel_minimum
#print axioms x_logical
#print axioms z_logical
#print axioms pauli_lower
#print axioms dX_eq_six
#print axioms dZ_eq_six
#print axioms d_eq_six
#print axioms exact_distance
#print axioms certified_public_code

end Qldpc1000
