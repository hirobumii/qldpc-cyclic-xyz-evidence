import Qec663Proof.Binding663.Bridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Binding663

/-- Membership is the ordinary binary row associated to a duplicate-free support. -/
def supportVector {n : Nat} (s : List Nat) : Vec n := fun i => decide (i.val ∈ s)

theorem ofSupport_eq_supportVector {n : Nat} (s : List Nat) (hs : s.Nodup) :
    (ofSupport s : Vec n) = supportVector s := by
  funext i
  induction s with
  | nil => simp [ofSupport, zero, supportVector]
  | cons j js ih =>
      have hnd := List.nodup_cons.mp hs
      have hi := ih hnd.2
      simp only [ofSupport, add, oneHot, supportVector] at *
      by_cases he : i.val = j
      · have hn : i.val ∉ js := by simpa [he] using hnd.1
        simp [hi, he, hnd.1]
      · simp [hi, he, List.mem_cons]

/-- Pure sparse intersection parity, with no trusted external result. -/
def supportDot : List Nat → List Nat → Bool
  | [], _ => false
  | i :: is, t => decide (i ∈ t) ^^ supportDot is t

theorem sparseParity_supportVector {n : Nat} (s t : List Nat)
    (hs : ∀ i ∈ s, i < n) :
    sparseParity s (supportVector (n := n) t) = supportDot s t := by
  induction s with
  | nil => rfl
  | cons i is ih =>
      rw [sparseParity, supportDot, ih (fun j hj => hs j (by simp [hj]))]
      simp [eval, hs i (by simp), supportVector]

theorem supportDot_eq_dot {n : Nat} (s t : List Nat)
    (hs : ∀ i ∈ s, i < n) (ht : t.Nodup) :
    supportDot s t = dot (ofSupport (n := n) s) (ofSupport t) := by
  rw [dot_ofSupport, ofSupport_eq_supportVector t ht]
  exact (sparseParity_supportVector s t hs).symm

/-- A transparent sparse check of every cross-sector stabilizer pair. -/
def cssCommutationCheck (xs zs : List (List Nat)) : Bool :=
  xs.all fun x => zs.all fun z => !(supportDot z x)

theorem cssCommutationCheck_sound {n : Nat} {xs zs : List (List Nat)}
    (h : cssCommutationCheck xs zs = true)
    (hxvalid : ∀ x ∈ xs, x.Nodup)
    (hzvalid : ∀ z ∈ zs, ∀ i ∈ z, i < n) :
    ∀ x ∈ xs, Kernel (n := n) zs (ofSupport x) := by
  intro x hx z hz
  rw [← supportDot_eq_dot z x (hzvalid z hz) (hxvalid x hx)]
  have hc := List.all_eq_true.mp (List.all_eq_true.mp h x hx) z hz
  cases hd : supportDot z x <;> simp_all

/-- Kernel subspaces are closed under true F₂ addition. -/
theorem kernel_zero {n : Nat} (rows : List (List Nat)) : Kernel (n := n) rows zero := by
  intro row _
  exact dot_zero_right _

theorem kernel_add {n : Nat} {rows : List (List Nat)} {u v : Vec n}
    (hu : Kernel rows u) (hv : Kernel rows v) : Kernel rows (add u v) := by
  intro row hr
  rw [dot_add_right, hu row hr, hv row hr]
  rfl

theorem rowSpan_in_kernel {n : Nat} {xs zs : List (List Nat)}
    (h : ∀ x ∈ xs, Kernel (n := n) zs (ofSupport x))
    {v : Vec n} (hv : RowSpan xs v) : Kernel zs v := by
  induction hv with
  | zero => exact kernel_zero zs
  | row hr => exact h _ hr
  | add _ _ ihu ihv => exact kernel_add ihu ihv

end Binding663
