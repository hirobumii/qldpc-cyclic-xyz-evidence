import Qldpc1000.CommutationConcrete
import Qldpc1000.Symmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Qldpc1000
namespace Cayley
open Commutation Symmetry

/-- The opposite product packages right Cayley graphs with the same symbolic
proof as left Cayley graphs. -/
def op (right : Bool) (x y : Fin 100) := if right then mul y x else mul x y

theorem assoc (r : Bool) (x y z : Fin 100) : op r (op r x y) z = op r x (op r y z) := by
  cases r <;> simp [op, mul_assoc]
@[simp] theorem unit_l (r : Bool) (x : Fin 100) : op r 0 x = x := by
  cases r <;> simp [op, unit_left, unit_right]
@[simp] theorem unit_r (r : Bool) (x : Fin 100) : op r x 0 = x := by
  cases r <;> simp [op, unit_left, unit_right]
@[simp] theorem inv_l (r : Bool) (x : Fin 100) : op r (inverse x) x = 0 := by
  cases r <;> simp [op, Symmetry.inverse_left, Symmetry.inverse_right]
@[simp] theorem inv_r (r : Bool) (x : Fin 100) : op r x (inverse x) = 0 := by
  cases r <;> simp [op, Symmetry.inverse_left, Symmetry.inverse_right]

theorem cancel_r (r : Bool) (x y u : Fin 100) (h : op r x u = op r y u) : x=y := by
  have he := congrArg (fun t => op r t (inverse u)) h
  simpa only [assoc, inv_r, unit_r] using he

theorem cancel_l (r : Bool) (u x y : Fin 100) (h : op r u x = op r u y) : x=y := by
  have he := congrArg (op r (inverse u)) h
  simpa only [← assoc, inv_l, unit_l] using he

/-- Six signed generators: A for left graphs and B for right graphs. -/
def signed (r : Bool) (i : Fin 6) : Fin 100 :=
  if i.val < 3 then if r then b (Fin.ofNat 3 i.val) else a (Fin.ofNat 3 i.val)
  else if r then bi (Fin.ofNat 3 (i.val-3)) else ai (Fin.ofNat 3 (i.val-3))

def difference (r : Bool) (s t : Fin 6) : Fin 100 :=
  op r (inverse (signed r s)) (signed r t)

def offDiagonal : List (Fin 6 × Fin 6) :=
  (List.finRange 6).flatMap fun s => (List.finRange 6).filterMap
    (fun t => if s=t then none else some (s,t))

/-- This certificate contains30 generator products, not graph vertices,
walks, cycles, supports, or a search tree. -/
theorem difference_distinct : ∀ r,
    (offDiagonal.map (fun st => difference r st.1 st.2)).Nodup := by decide
theorem difference_count : offDiagonal.length = 30 := by decide
theorem signed_injective : ∀ r s t, signed r s = signed r t → s=t := by decide
theorem signed_odd : ∀ r s, (second (signed r s)).val % 2 = 1 := by decide

theorem mem_offDiagonal (s t : Fin 6) (h : s≠t) : (s,t)∈offDiagonal := by
  apply List.mem_flatMap.mpr
  refine ⟨s, List.mem_finRange _, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨t, List.mem_finRange _, by simp [h]⟩

theorem nodup_map_injective {α β : Type} (f : α → β) (s : List α)
    (nd : (s.map f).Nodup) (a b : α) (ha : a∈s) (hb : b∈s) (he : f a=f b) : a=b := by
  induction s with
  | nil => simp at ha
  | cons q qs ih =>
    have hn := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with hqa | ha
    · subst a
      rcases List.mem_cons.mp hb with hqb | hb
      · exact hqb.symm
      · exact False.elim (hn.1 (List.mem_map.mpr ⟨b,hb,he.symm⟩))
    · rcases List.mem_cons.mp hb with hqb | hb
      · subst b
        exact False.elim (hn.1 (List.mem_map.mpr ⟨a,ha,he⟩))
      · exact ih hn.2 ha hb

theorem difference_injective (r : Bool) (s t u v : Fin 6) (hst : s≠t) (huv : u≠v)
    (h : difference r s t = difference r u v) : s=u ∧ t=v := by
  have he := @nodup_map_injective (Fin 6 × Fin 6) (Fin 100)
    (fun st => difference r st.1 st.2) offDiagonal
    (difference_distinct r) (s,t) (u,v) (mem_offDiagonal s t hst) (mem_offDiagonal u v huv) h
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

/-- Two distinct vertices cannot have two distinct common neighbors in a
Cayley graph whose30 nontrivial signed differences are distinct. All four
vertices and all translations here are symbolic. -/
theorem common_neighbors (r : Bool) (x y p q : Fin 100)
    (s t u v : Fin 6)
    (hp : p = op r (signed r s) x) (hp' : p = op r (signed r t) y)
    (hq : q = op r (signed r u) x) (hq' : q = op r (signed r v) y) : x=y ∨ p=q := by
  by_cases hxy : x=y
  · exact Or.inl hxy
  have hst : t≠s := by
    intro he
    have hh := hp.symm.trans hp'
    rw [he] at hh
    exact hxy (cancel_l r _ _ _ hh)
  have huv : v≠u := by
    intro he
    have hh := hq.symm.trans hq'
    rw [he] at hh
    exact hxy (cancel_l r _ _ _ hh)
  have hd1 : op r (difference r t s) x = y := by
    have he := congrArg (op r (inverse (signed r t))) (hp.symm.trans hp')
    simpa only [difference, ← assoc, inv_l, unit_l] using he
  have hd2 : op r (difference r v u) x = y := by
    have he := congrArg (op r (inverse (signed r v))) (hq.symm.trans hq')
    simpa only [difference, ← assoc, inv_l, unit_l] using he
  have hd := cancel_r r _ _ x (hd1.trans hd2.symm)
  have hi := difference_injective r t s v u hst huv hd
  exact Or.inr (by rw [hp,hq,hi.2])

def evenVertex (u : Fin 100) : Prop := (second u).val % 2 = 0
instance (u : Fin 100) : Decidable (evenVertex u) := inferInstanceAs (Decidable (_ % 2 = 0))

theorem phase_add (r : Bool) (x y : Fin 100) :
    (second (op r x y)).val % 2 = ((second x).val + (second y).val) % 2 := by
  cases r <;> simp only [op, Bool.false_eq_true, ↓reduceIte, mul, second_pack, Fin.val_add] <;> omega

theorem signed_flips (r : Bool) (s : Fin 6) (u : Fin 100) :
    evenVertex (op r (signed r s) u) ↔ ¬ evenVertex u := by
  unfold evenVertex
  rw [phase_add]
  have hs := signed_odd r s
  omega

end Cayley
end Qldpc1000
