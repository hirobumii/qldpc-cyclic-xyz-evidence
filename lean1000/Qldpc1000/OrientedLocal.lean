import Qldpc1000.LocalFormula
import Qldpc1000.Cayley
import Qldpc1000.Shores

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Qldpc1000
namespace AlgebraicLocal
open Commutation Symmetry Cayley LocalFormula

def baseIndex (z cc : Bool) (b : Fin 3) (l : Fin 10) : Fin 3 :=
  if cc then b else if z then Fin.ofNat 3 (l.val%3) else Fin.ofNat 3 (l.val/3)

def mkSign (k : Fin 3) (positive : Bool) : Fin 6 :=
  ⟨k.val + (if positive then 0 else 3), by have := k.isLt; cases positive <;> simp <;> omega⟩

theorem signed_mk : ∀ r k positive, signed r (mkSign k positive) =
    (if positive then (if r then b k else a k) else (if r then bi k else ai k)) := by decide

theorem flip_signed : ∀ r k positive,
    inverse (signed r (mkSign k positive)) = signed r (mkSign k (!positive)) := by decide

theorem mkSign_injective (k l : Fin 3) (p q : Bool) (h : mkSign k p = mkSign l q) :
    k=l ∧ p=q := by
  have he := congrArg Fin.val h
  have hk := k.isLt
  have hl := l.isLt
  cases p <;> cases q <;> simp_all [mkSign, Fin.ext_iff] <;> omega

theorem step_formula (z cc : Bool) (b : Fin 3) (l : Fin 10) (u : Fin 100) :
    edgeStep z cc b l u = op (z ^^ cc) (signed (z ^^ cc) (mkSign (baseIndex z cc b l) z)) u := by
  rw [signed_mk]
  cases z <;> cases cc <;> simp [edgeStep, op, baseIndex, left, right, leftInv, rightInv]

theorem step_inverse (z cc : Bool) (b : Fin 3) (l : Fin 10) (u : Fin 100) :
    op (z ^^ cc) (signed (z ^^ cc) (mkSign (baseIndex z cc b l) (!z)))
      (edgeStep z cc b l u) = u := by
  rw [← flip_signed, step_formula, ← assoc, inv_l, unit_l]

theorem step_flips (z cc : Bool) (b : Fin 3) (l : Fin 10) (u : Fin 100) :
    evenVertex (edgeStep z cc b l u) ↔ ¬evenVertex u := by
  rw [step_formula]
  exact signed_flips _ _ _

def leftEnd (z cc : Bool) (b : Fin 3) (q : Fin 1000) : Fin 100 :=
  if evenVertex (vertex q) then vertex q else edgeStep z cc b (label q) (vertex q)
def rightEnd (z cc : Bool) (b : Fin 3) (q : Fin 1000) : Fin 100 :=
  if evenVertex (vertex q) then edgeStep z cc b (label q) (vertex q) else vertex q
def edgeLabel (z cc : Bool) (b : Fin 3) (q : Fin 1000) : Fin 6 :=
  mkSign (baseIndex z cc b (label q)) (if evenVertex (vertex q) then z else !z)

theorem oriented_step (z cc : Bool) (b : Fin 3) (q : Fin 1000) :
    rightEnd z cc b q = op (z ^^ cc) (signed (z ^^ cc) (edgeLabel z cc b q)) (leftEnd z cc b q) := by
  by_cases h : evenVertex (vertex q)
  · simpa [leftEnd, rightEnd, edgeLabel, h] using step_formula z cc b (label q) (vertex q)
  · simpa [leftEnd, rightEnd, edgeLabel, h] using (step_inverse z cc b (label q) (vertex q)).symm

theorem shores (z cc : Bool) (b : Fin 3) (q : Fin 1000) :
    evenVertex (leftEnd z cc b q) ∧ ¬evenVertex (rightEnd z cc b q) := by
  have hs := step_flips z cc b (label q) (vertex q)
  by_cases h : evenVertex (vertex q) <;> simp_all [leftEnd, rightEnd]

/-- For one block and one VV/CC class, the physical block label is recovered
from its generator index. These are only10 physical block labels. -/
theorem label_recovery : ∀ z cc b (l m : Fin 10),
    expectedKind z (put l 0) = targetKind cc b →
    expectedKind z (put m 0) = targetKind cc b →
    baseIndex z cc b l = baseIndex z cc b m → l=m := by decide

theorem edge_simple (z cc : Bool) (b : Fin 3) (q r : Fin 1000)
    (hq : expectedKind z q = targetKind cc b) (hr : expectedKind z r = targetKind cc b)
    (he : leftEnd z cc b q = leftEnd z cc b r)
    (ho : rightEnd z cc b q = rightEnd z cc b r) : q=r := by
  have hs : op (z ^^ cc) (signed (z ^^ cc) (edgeLabel z cc b q)) (leftEnd z cc b q) =
      op (z ^^ cc) (signed (z ^^ cc) (edgeLabel z cc b r)) (leftEnd z cc b q) := by
    rw [← oriented_step, ho, he, ← oriented_step]
  have hi := signed_injective _ _ _ (cancel_r _ _ _ _ hs)
  have hparts := mkSign_injective _ _ _ _ hi
  have hl : label q = label r := by
    apply label_recovery z cc b _ _
    · simpa [expectedKind] using hq
    · simpa [expectedKind] using hr
    · exact hparts.1
  have hc : evenVertex (vertex q) ↔ evenVertex (vertex r) := by
    have hh := hparts.2
    cases z <;> by_cases hq' : evenVertex (vertex q) <;>
      by_cases hr' : evenVertex (vertex r) <;> simp_all
  have hv : vertex q = vertex r := by
    by_cases h : evenVertex (vertex q)
    · simpa [leftEnd, h, hc.mp h] using he
    · have hh : ¬evenVertex (vertex r) := fun h' => h (hc.mpr h')
      simpa [rightEnd, h, hh] using ho
  calc q = put (label q) (vertex q) := (put_parts q).symm
       _ = put (label r) (vertex r) := by rw [hl,hv]
       _ = r := put_parts r

/-- A rectangle among four arbitrary physical edges would give two distinct
common neighbors in the signed-generator Cayley graph. CC edges are a
single-generator subgraph, so the same theorem covers them. -/
theorem no_rectangle (z cc : Bool) (b : Fin 3) (q r s t : Fin 1000)
    (hq : expectedKind z q = targetKind cc b) (hr : expectedKind z r = targetKind cc b)
    (hs : expectedKind z s = targetKind cc b) (ht : expectedKind z t = targetKind cc b)
    (hqr : leftEnd z cc b q = leftEnd z cc b r)
    (hst : leftEnd z cc b s = leftEnd z cc b t)
    (hqs : rightEnd z cc b q = rightEnd z cc b s)
    (hrt : rightEnd z cc b r = rightEnd z cc b t) : q=r ∨ q=s := by
  have hn := common_neighbors (z ^^ cc) (leftEnd z cc b q) (leftEnd z cc b s)
    (rightEnd z cc b q) (rightEnd z cc b r)
    (edgeLabel z cc b q) (edgeLabel z cc b s) (edgeLabel z cc b r) (edgeLabel z cc b t)
    (oriented_step z cc b q)
    (by rw [hqs]; exact oriented_step z cc b s)
    (by rw [hqr]; exact oriented_step z cc b r)
    (by rw [hrt,hst]; exact oriented_step z cc b t)
  rcases hn with hl | hr'
  · exact Or.inr (edge_simple z cc b q s hq hs hl hqs)
  · exact Or.inl (edge_simple z cc b q r hq hr hqr hr')

theorem formula_endpoints (z cc : Bool) (b : Fin 3) (q : Fin 1000)
    (h : expectedKind z q = targetKind cc b) :
    decode 100 (formulaColumn z cc b q) =
      add (oneHot (leftEnd z cc b q).val) (oneHot (rightEnd z cc b q).val) := by
  by_cases he : evenVertex (vertex q)
  · simp [formulaColumn, h, decode_xor, decode_pow, leftEnd, rightEnd, he]
  · simp only [formulaColumn, h, ↓reduceIte, decode_xor, decode_pow, leftEnd, rightEnd, he]
    funext i
    exact Bool.xor_comm _ _

theorem no_small (z cc : Bool) (b : Fin 3) (s : List (Fin 1000))
    (nd : s.Nodup) (ne : s≠[]) (small : s.length≤5) (even : s.length%2=0)
    (good : ∀ q∈s, kind z q = targetKind cc b) : syndrome (formulaColumn z cc b) s ≠ 0 := by
  intro hz
  have hg : ∀ q∈s, expectedKind z q = targetKind cc b := by
    intro q hq; rw [← kind_formula]; exact good q hq
  have hshore := shore_syndromes_zero evenVertex (leftEnd z cc b) (rightEnd z cc b)
    (formulaColumn z cc b) s
    (fun q hq => formula_endpoints z cc b q (hg q hq))
    (fun q _ => (shores z cc b q).1) (fun q _ => (shores z cc b q).2) hz
  exact small_bipartite_impossible (fun q => (leftEnd z cc b q).val)
    (fun q => (rightEnd z cc b q).val) (fun q => expectedKind z q = targetKind cc b)
    (fun a c ha hc hl hr => edge_simple z cc b a c ha hc (Fin.ext hl) (Fin.ext hr))
    (fun a c d e ha hc hd he h1 h2 h3 h4 => no_rectangle z cc b a c d e ha hc hd he
      (Fin.ext h1) (Fin.ext h2) (Fin.ext h3) (Fin.ext h4))
    s nd ne small even hg hshore.1 hshore.2

end AlgebraicLocal
end Qldpc1000
