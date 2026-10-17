import Std

/-! Finite phase-free binary symplectic Paulis. All arithmetic is over F₂. -/
namespace QLDPC

structure Pauli (n : Nat) where
  x : BitVec n
  z : BitVec n
  deriving DecidableEq, Repr

namespace Pauli

def zero : Pauli n := ⟨0, 0⟩
def add (p q : Pauli n) : Pauli n := ⟨p.x ^^^ q.x, p.z ^^^ q.z⟩
def support (p : Pauli n) : List Nat :=
  (List.range n).filter (fun i => p.x.getLsbD i || p.z.getLsbD i)
def weight (p : Pauli n) : Nat := p.support.length
def localSymplectic (p q : Pauli n) (i : Nat) : Bool :=
  (p.x.getLsbD i && q.z.getLsbD i) ^^ (p.z.getLsbD i && q.x.getLsbD i)
def symplectic (p q : Pauli n) : Bool :=
  ((List.range n).map (p.localSymplectic q)).foldl (· ^^ ·) false

def ofSupports (xs zs : List Nat) : Pauli n :=
  ⟨xs.foldl (fun v i => v ||| ((1 : BitVec n) <<< i)) 0,
   zs.foldl (fun v i => v ||| ((1 : BitVec n) <<< i)) 0⟩

@[simp] theorem add_x (p q : Pauli n) : (p.add q).x = p.x ^^^ q.x := rfl
@[simp] theorem add_z (p q : Pauli n) : (p.add q).z = p.z ^^^ q.z := rfl

end Pauli

def Commutes (p q : Pauli n) : Prop := p.symplectic q = false

def Normalizes (S : List (Pauli n)) (p : Pauli n) : Prop :=
  ∀ g ∈ S, Commutes p g

def PairwiseCommute (S : List (Pauli n)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, Commutes p q

/-- The F₂ row span, defined by closure under zero and vector addition. -/
inductive InSpan (S : List (Pauli n)) : Pauli n → Prop where
  | zero : InSpan S Pauli.zero
  | of_mem {p : Pauli n} : p ∈ S → InSpan S p
  | add {p q : Pauli n} : InSpan S p → InSpan S q → InSpan S (p.add q)

/-- A phase-free nontrivial logical Pauli. -/
def Logical (S : List (Pauli n)) (p : Pauli n) : Prop :=
  Normalizes S p ∧ ¬ InSpan S p

/-- Exact distance, including both a lower bound and a nontrivial witness. -/
def HasDistance (S : List (Pauli n)) (d : Nat) : Prop :=
  (∀ p, Logical S p → d ≤ p.weight) ∧
  (∃ p, Logical S p ∧ p.weight = d)

end QLDPC
