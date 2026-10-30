import Qldpc1000.MaskBridge

namespace Qldpc1000

/-- A bulk Boolean array certificate applies also to defaulted lookups when
its predicate holds at the default. No table-indexing oracle is assumed. -/
theorem all_getD {α : Type} [Inhabited α] (a : Array α) (p : α → Bool)
    (ha : a.toList.all p = true) (hd : p default = true) (i : Nat) : p a[i]! = true := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi]
    apply List.all_eq_true.mp ha
    simp
  · simp [getElem!_neg a i hi, hd]

/-- Compact sparse masks have the same XOR semantics as ofSupport. -/
def supportMask : List Nat → Nat
  | [] => 0
  | i :: is => (2^i) ^^^ supportMask is

theorem decode_pow (n i : Nat) : decode n (2^i) = oneHot i := by
  funext q
  simp [decode, oneHot, Nat.testBit_two_pow, eq_comm]

theorem decode_supportMask (s : List Nat) : decode n (supportMask s) = ofSupport s := by
  induction s with
  | nil => exact decode_zero n
  | cons i is ih => simp only [supportMask, decode_xor, decode_pow, ih, ofSupport]

theorem all_zip_getD {α β : Type} [Inhabited α] [Inhabited β]
    (a : Array α) (b : Array β) (p : α → β → Bool)
    (h : (a.toList.zip b.toList).all (fun ab => p ab.1 ab.2) = true)
    (i : Nat) (ha : i < a.size) (hb : i < b.size) : p a[i]! b[i]! = true := by
  have hi : i < (a.toList.zip b.toList).length := by simp; omega
  have hm := List.getElem_mem hi
  have hp := List.all_eq_true.mp h _ hm
  simpa [List.getElem_zip, getElem!_pos a i ha, getElem!_pos b i hb] using hp

/-- Transpose a list of binary column masks into one binary row mask. -/
def bitSlice : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, r => (c.testBit r).toNat ^^^ (bitSlice cs r <<< 1)

theorem testBit_bitSlice (cs : List Nat) (r q : Nat) :
    (bitSlice cs r).testBit q = cs[q]!.testBit r := by
  induction cs generalizing q with
  | nil => simp [bitSlice]
  | cons c cs ih =>
    cases q with
    | zero => cases h : c.testBit r <;> simp [bitSlice, h]
    | succ q =>
      simp only [bitSlice, Nat.testBit_xor, Nat.testBit_shiftLeft, List.getElem!_cons_succ]
      rw [show q.succ - 1 = q by omega, ih]
      cases h : c.testBit r <;> simp [Nat.testBit_succ]

theorem mem_zip_getD {α β : Type} [Inhabited α] [Inhabited β]
    (a : Array α) (b : Array β) (i : Nat) (ha : i < a.size) (hb : i < b.size) :
    (a[i]!, b[i]!) ∈ a.toList.zip b.toList := by
  have hi : i < (a.toList.zip b.toList).length := by simp; omega
  have hm := List.getElem_mem hi
  simpa [List.getElem_zip, getElem!_pos a i ha, getElem!_pos b i hb] using hm

theorem ofSupport_true_mem (row : List Nat) (q : Fin n)
    (h : ofSupport row q = true) : q.val ∈ row := by
  induction row with
  | nil => cases h
  | cons i is ih =>
    by_cases hq : q.val = i
    · simp [hq]
    · have ht : ofSupport is q = true := by simpa [ofSupport, add, oneHot, hq] using h
      exact List.mem_cons_of_mem i (ih ht)

end Qldpc1000
