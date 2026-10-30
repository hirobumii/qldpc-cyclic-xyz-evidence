import Qldpc1000.OrientedLocal

namespace Qldpc1000
namespace AlgebraicLocal
open Commutation Symmetry Cayley LocalFormula

theorem oneHot_injective (u v : Fin n) (h : (oneHot u.val : Vec n) = oneHot v.val) : u=v := by
  have hh := congrFun h u
  have he : u.val = v.val := by simpa [oneHot] using hh.symm
  exact Fin.ext he

/-- Equality of two bipartite boundaries identifies the endpoints shore by
shore, without enumerating pairs of physical edges. -/
theorem shore_boundary_injective (p : Fin n → Prop) [DecidablePred p]
    (a b c d : Fin n) (ha : p a) (hb : ¬p b) (hc : p c) (hd : ¬p d)
    (h : add (n := n) (oneHot a.val) (oneHot b.val) = add (oneHot c.val) (oneHot d.val)) :
    a=c ∧ b=d := by
  constructor
  · apply oneHot_injective
    have hh := congrArg (restrictMap p) h
    rw [(restrictMap p).map_add, (restrictMap p).map_add,
      restrict_basis p a ha, restrict_basis_zero p b hb,
      restrict_basis p c hc, restrict_basis_zero p d hd] at hh
    funext i
    have he := congrFun hh i
    simpa only [Qldpc1000.add, Qldpc1000.zero, Bool.xor_false, Bool.false_xor] using he
  · apply oneHot_injective
    have hh := congrArg (restrictMap (fun u => ¬p u)) h
    rw [(restrictMap (fun u => ¬p u)).map_add, (restrictMap (fun u => ¬p u)).map_add,
      restrict_basis_zero (fun u => ¬p u) a (by simpa using ha),
      restrict_basis (fun u => ¬p u) b hb,
      restrict_basis_zero (fun u => ¬p u) c (by simpa using hc),
      restrict_basis (fun u => ¬p u) d hd] at hh
    funext i
    have he := congrFun hh i
    simpa only [Qldpc1000.add, Qldpc1000.zero, Bool.xor_false, Bool.false_xor] using he

theorem phase_op (r : Bool) (x y : Fin 100) : second (op r x y) = second x + second y := by
  cases r <;> simp only [op, Bool.false_eq_true, ↓reduceIte, mul, second_pack]
  apply Fin.ext
  simp only [Fin.val_add, Nat.add_comm]

theorem phase_cancel (a b c : Fin 20) (h : a+c=b+c) : a=b := by
  have he := congrArg Fin.val h
  simp only [Fin.val_add] at he
  apply Fin.ext
  have := a.isLt; have := b.isLt; have := c.isLt
  omega

/-- VV and CC cannot share an edge when their signed phase increments are
disjoint. Arbitrary physical vertices are eliminated symbolically. -/
theorem formula_nonedge (z : Bool) (b : Fin 3)
    (sep : ∀ i positive, second (signed z i) ≠ second (signed (!z) (mkSign b positive)))
    (q u : Fin 1000)
    (hq : expectedKind z q = targetKind false b) (hu : expectedKind z u = targetKind true b) :
    formulaColumn z false b q ≠ formulaColumn z true b u := by
  intro he
  have hv := congrArg (decode 100) he
  rw [formula_endpoints z false b q hq, formula_endpoints z true b u hu] at hv
  have ends := shore_boundary_injective evenVertex _ _ _ _
    (shores z false b q).1 (shores z false b q).2
    (shores z true b u).1 (shores z true b u).2 hv
  have hphase : second (signed (z ^^ false) (edgeLabel z false b q)) + second (leftEnd z false b q) =
      second (signed (z ^^ true) (edgeLabel z true b u)) + second (leftEnd z false b q) := by
    rw [← phase_op, ← oriented_step, ends.2, ends.1, ← phase_op, ← oriented_step]
  have hi := phase_cancel _ _ _ hphase
  simp only [Bool.xor_false, Bool.xor_true] at hi
  have hc : edgeLabel z true b u = mkSign b (if evenVertex (vertex u) then z else !z) := by
    simp [edgeLabel,baseIndex]
  rw [hc] at hi
  exact sep _ _ hi

end AlgebraicLocal
end Qldpc1000
