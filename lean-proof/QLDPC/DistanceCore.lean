import QLDPC.Basic

namespace QLDPC

/-! A kernel-checkable certificate for the absence of normalizers of weight 1–3.
The certificate concerns exact singleton-error syndromes, and the theorem below
bridges it to every binary-symplectic Pauli, via its actual support. -/
namespace DistanceProof

def parity (l : List Bool) : Bool := l.foldr (· ^^ ·) false

def vxor {m : Nat} (l : List (BitVec m)) : BitVec m := l.foldr (· ^^^ ·) 0

theorem foldl_parity (l : List Bool) (a : Bool) :
    l.foldl (· ^^ ·) a = (a ^^ parity l) := by
  induction l generalizing a with
  | nil => simp [parity]
  | cons b l ih => simp [parity, ih, Bool.xor_assoc]

theorem parity_filter (l : List α) (keep : α → Bool) (f : α → Bool)
    (hz : ∀ a ∈ l, keep a = false → f a = false) :
    parity (l.map f) = parity ((l.filter keep).map f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hz' : ∀ a ∈ l, keep a = false → f a = false :=
      fun a ha => hz a (by simp [ha])
    have ih' := ih hz'
    cases hk : keep a with
    | false => simpa [parity, hk, hz a (by simp) hk] using ih'
    | true => simpa only [parity, List.filter_cons_of_pos hk, List.map_cons, List.foldr_cons, Bool.xor_right_inj] using ih'

theorem symplectic_support (p g : Pauli n) :
    p.symplectic g = parity (p.support.map (p.localSymplectic g)) := by
  rw [Pauli.symplectic, foldl_parity]
  simp only [Bool.false_xor]
  apply parity_filter
  intro i _ hi
  simp only [Bool.or_eq_false_iff] at hi
  simp [Pauli.localSymplectic, hi.1, hi.2]

theorem getLsbD_vxor (l : List (BitVec m)) (j : Nat) :
    (vxor l).getLsbD j = parity (l.map (fun v => v.getLsbD j)) := by
  induction l with
  | nil => simp [vxor, parity]
  | cons v l ih => simpa only [vxor, parity, List.foldr_cons, List.map_cons, BitVec.getLsbD_xor, Bool.xor_right_inj] using ih

/-- A finite search tree used only as a Boolean predicate, never as an axiom. -/
inductive SyndromeTree where
  | empty
  | node (value : Nat) (left right : SyndromeTree)
  deriving Repr

def SyndromeTree.contains : SyndromeTree → Nat → Bool
  | .empty, _ => false
  | .node v l r, x => if x = v then true else if x < v then l.contains x else r.contains x

/-- X, Z, and Y singleton syndromes, in that order. -/
def axiscol (xc zc : Nat → BitVec m) (i : Nat) (a : Fin 3) : BitVec m :=
  if a.val = 0 then xc i else if a.val = 1 then zc i else xc i ^^^ zc i

structure Certificate (n m : Nat) (S : List (Pauli n)) where
  xc : Nat → BitVec m
  zc : Nat → BitVec m
  row : Fin m → Pauli n
  row_mem : ∀ j, row j ∈ S
  bind_x : ∀ (i : Fin n) (j : Fin m), (xc i).getLsbD j = (row j).z.getLsbD i
  bind_z : ∀ (i : Fin n) (j : Fin m), (zc i).getLsbD j = (row j).x.getLsbD i
  allowed : BitVec m → Bool
  zero_allowed : allowed 0 = true
  single_allowed : ∀ (i : Fin n) (a : Fin 3), allowed (axiscol xc zc i a) = true
  single_nonzero : ∀ (i : Fin n) (a : Fin 3), axiscol xc zc i a ≠ 0
  pair_forbidden : ∀ (i j : Fin n) (a b : Fin 3), i ≠ j →
    allowed (axiscol xc zc i a ^^^ axiscol xc zc j b) = false

namespace Certificate

variable {S : List (Pauli n)} (C : Certificate n m S)

def localSyndrome (p : Pauli n) (i : Nat) : BitVec m :=
  (if p.x.getLsbD i then C.xc i else 0) ^^^
  (if p.z.getLsbD i then C.zc i else 0)

theorem support_lt (p : Pauli n) (hi : i ∈ p.support) : i < n := by
  exact List.mem_range.mp (List.mem_filter.mp hi).1

theorem support_nonzero (p : Pauli n) (hi : i ∈ p.support) :
    (p.x.getLsbD i || p.z.getLsbD i) = true := (List.mem_filter.mp hi).2

theorem local_axis (p : Pauli n) (hi : i ∈ p.support) :
    ∃ a : Fin 3, C.localSyndrome p i = axiscol C.xc C.zc i a := by
  have hz := support_nonzero p hi
  cases hx : p.x.getLsbD i <;> cases hz' : p.z.getLsbD i
  · simp [hx, hz'] at hz
  · exact ⟨⟨1, by decide⟩, by simp [localSyndrome, axiscol, hx, hz']⟩
  · exact ⟨⟨0, by decide⟩, by simp [localSyndrome, axiscol, hx, hz']⟩
  · exact ⟨⟨2, by decide⟩, by simp [localSyndrome, axiscol, hx, hz']⟩

theorem local_nonzero (p : Pauli n) (hi : i ∈ p.support) : C.localSyndrome p i ≠ 0 := by
  obtain ⟨a, ha⟩ := C.local_axis p hi
  rw [ha]
  exact C.single_nonzero ⟨i, support_lt p hi⟩ a

theorem local_allowed (p : Pauli n) (hi : i ∈ p.support) :
    C.allowed (C.localSyndrome p i) = true := by
  obtain ⟨a, ha⟩ := C.local_axis p hi
  rw [ha]
  exact C.single_allowed ⟨i, support_lt p hi⟩ a

theorem local_pair_forbidden (p : Pauli n) (hi : i ∈ p.support) (hj : j ∈ p.support)
    (hne : i ≠ j) : C.allowed (C.localSyndrome p i ^^^ C.localSyndrome p j) = false := by
  obtain ⟨a, ha⟩ := C.local_axis p hi
  obtain ⟨b, hb⟩ := C.local_axis p hj
  rw [ha, hb]
  exact C.pair_forbidden ⟨i, support_lt p hi⟩ ⟨j, support_lt p hj⟩ a b
    (fun h => hne (congrArg Fin.val h))

theorem local_bit (p : Pauli n) (hi : i ∈ p.support) (j : Fin m) :
    (C.localSyndrome p i).getLsbD j = p.localSymplectic (C.row j) i := by
  have hx := C.bind_x ⟨i, support_lt p hi⟩ j
  have hz := C.bind_z ⟨i, support_lt p hi⟩ j
  simp only [Fin.val_mk] at hx hz
  have hx' : (C.xc i)[j.val] = (C.row j).z.getLsbD i := by simpa using hx
  have hz' : (C.zc i)[j.val] = (C.row j).x.getLsbD i := by simpa using hz
  cases hpx : p.x.getLsbD i <;> cases hpz : p.z.getLsbD i <;>
    simp [localSyndrome, Pauli.localSymplectic, hpx, hpz, hx', hz']

theorem normalizer_syndrome (p : Pauli n) (hp : Normalizes S p) :
    vxor (p.support.map (C.localSyndrome p)) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_vxor]
  simp only [List.map_map, Function.comp_def]
  have hmap : p.support.map (fun i => (C.localSyndrome p i).getLsbD j) =
      p.support.map (p.localSymplectic (C.row ⟨j, hj⟩)) :=
    List.map_congr_left (fun i hi => C.local_bit p hi ⟨j, hj⟩)
  rw [hmap, ← symplectic_support]
  simpa [Commutes] using hp (C.row ⟨j, hj⟩) (C.row_mem ⟨j, hj⟩)

theorem support_nodup (p : Pauli n) : p.support.Nodup :=
  List.Pairwise.filter _ List.nodup_range

include C in
/-- Every normalizer has either empty support or at least four sites. -/
theorem no_small_normalizer (p : Pauli n) (hp : Normalizes S p) (hw : p.weight < 4) :
    p.weight = 0 := by
  have hs := C.normalizer_syndrome p hp
  have hn := support_nodup p
  unfold Pauli.weight at hw ⊢
  cases he : p.support with
  | nil => rfl
  | cons i tail =>
    have hi : i ∈ p.support := by simp [he]
    cases ht : tail with
    | nil =>
      have hz : C.localSyndrome p i = 0 := by simpa [he, ht, vxor] using hs
      exact False.elim (C.local_nonzero p hi hz)
    | cons j tail =>
      have hj : j ∈ p.support := by simp [he, ht]
      have hij : i ≠ j := by
        have hh := (List.nodup_cons.mp (show (i :: j :: tail).Nodup from by simpa [he, ht] using hn)).1
        intro hij
        apply hh
        simp [hij]
      cases hu : tail with
      | nil =>
        have hz : C.localSyndrome p i ^^^ C.localSyndrome p j = 0 := by
          simpa [he, ht, hu, vxor] using hs
        have hf := C.local_pair_forbidden p hi hj hij
        rw [hz, C.zero_allowed] at hf
        contradiction
      | cons k tail =>
        have hk : k ∈ p.support := by simp [he, ht, hu]
        have htail : tail = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp [he, ht, hu] at hw
          omega
        have hz : C.localSyndrome p i ^^^ C.localSyndrome p j = C.localSyndrome p k := by
          apply BitVec.xor_eq_zero_iff.mp
          simpa [he, ht, hu, htail, vxor, BitVec.xor_assoc] using hs
        have hf := C.local_pair_forbidden p hi hj hij
        rw [hz, C.local_allowed p hk] at hf
        contradiction

theorem weight_zero_eq_zero (p : Pauli n) (hw : p.weight = 0) : p = Pauli.zero := by
  have he : p.support = [] := List.eq_nil_of_length_eq_zero hw
  have hbits : ∀ i, i < n → p.x.getLsbD i = false ∧ p.z.getLsbD i = false := by
    intro i hi
    have hn : i ∉ p.support := by simp [he]
    have hb : (p.x.getLsbD i || p.z.getLsbD i) = false := by
      cases h : p.x.getLsbD i || p.z.getLsbD i with
      | false => rfl
      | true => exact False.elim (hn (List.mem_filter.mpr ⟨List.mem_range.mpr hi, h⟩))
    exact Bool.or_eq_false_iff.mp hb
  have hx : p.x = 0 := BitVec.eq_of_getLsbD_eq (fun i hi => by simpa using (hbits i hi).1)
  have hz : p.z = 0 := BitVec.eq_of_getLsbD_eq (fun i hi => by simpa using (hbits i hi).2)
  change Pauli.mk p.x p.z = Pauli.mk 0 0
  rw [hx, hz]

include C in
/-- The certificate implies the usual logical-distance lower bound. -/
theorem logical_weight_ge_four (p : Pauli n) (hp : Logical S p) : 4 ≤ p.weight := by
  by_cases h : 4 ≤ p.weight
  · exact h
  · have hw : p.weight < 4 := by omega
    have hz := C.no_small_normalizer p hp.1 hw
    have he := weight_zero_eq_zero p hz
    exact False.elim (hp.2 (he ▸ InSpan.zero))

end Certificate

end DistanceProof
end QLDPC
