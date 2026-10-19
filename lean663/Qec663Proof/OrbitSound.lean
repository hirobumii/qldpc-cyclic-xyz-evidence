import Qec663Proof.OrbitCoverage
import Qec663Proof.CheckerSoundness
import Qec663Proof.EnumerationNodup

/-! Unique syndrome-orbit keys and stabilizer containment imply injectivity
on every translated support. The resulting theorem proves the unchanged full
half4 checker proposition without evaluating its full list. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace QEC663.Orbit
open QEC663.Finite QEC663.Architecture

def orbitKey (column : Coord → BitVec 39) (s : Support) : Nat :=
  (minRotation (syndrome column s.val)).toNat

def stabilizerCheck (column : Coord → BitVec 39) (s : Support) : Bool :=
  let syn := syndrome column s.val
  (List.finRange 39).all (fun r =>
    if rotate r syn = syn
    then decide (act r s = s) else true)

def checkOrbit (column : Coord → BitVec 39) : Bool :=
  strictlyIncreasing ((representatives.map (orbitKey column)).mergeSort (· ≤ ·)) &&
    representatives.all (stabilizerCheck column)

theorem representatives_keys_unique (column : Coord → BitVec 39)
    (h : checkOrbit column = true) (r t : Support)
    (hr : r ∈ representatives) (ht : t ∈ representatives)
    (he : orbitKey column r = orbitKey column t) : r = t := by
  have hn := strictlyIncreasing_nodup _ (Bool.and_eq_true_iff.mp h).1
  have hn' : (representatives.map (orbitKey column)).Nodup :=
    hn.perm (List.mergeSort_perm _ _)
  exact map_nodup_injective_on (orbitKey column) representatives hn' r hr t ht he

theorem checked_stabilizers (column : Coord → BitVec 39)
    (h : checkOrbit column = true) (s : Support) (hs : s ∈ representatives)
    (r : Shift) (he : rotate r (syndrome column s.val) = syndrome column s.val) :
    act r s = s := by
  have ha := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 s hs
  have hb := List.all_eq_true.mp ha r (List.mem_finRange r)
  simpa only [he, ite_true, decide_eq_true_eq] using hb

theorem act_right_neg (r : Shift) (s : Support) : act r (act (neg r) s) = s := by
  rw [act_plus]
  have he : plus r (neg r) = 0 := by
    apply Fin.ext
    simp only [plus, neg]
    have := r.isLt
    omega
  rw [he, act_zero]

theorem orbit_local_injective (column : Coord → BitVec 39) (eqv : Equivariant column)
    (h : checkOrbit column = true) (s : Support) (hs : s ∈ representatives)
    (r t : Shift)
    (he : syndrome column (act r s).val = syndrome column (act t s).val) :
    act r s = act t s := by
  rw [syndrome_act column eqv, syndrome_act column eqv] at he
  have hf : rotate (plus (neg r) t) (syndrome column s.val) = syndrome column s.val := by
    rw [← rotate_plus, ← he, rotate_neg]
  have hg := checked_stabilizers column h s hs (plus (neg r) t) hf
  rw [← act_plus] at hg
  have hi := congrArg (act r) hg
  rw [act_right_neg] at hi
  exact hi.symm

theorem checkOrbit_injective (column : Coord → BitVec 39) (eqv : Equivariant column)
    (h : checkOrbit column = true) (s t : Support)
    (hs : s.val.Nodup) (ht : t.val.Nodup)
    (hls : s.val.length ≤ 4) (hlt : t.val.length ≤ 4)
    (he : syndrome column s.val = syndrome column t.val) : s = t := by
  obtain ⟨a, ha, r, hr⟩ := representative_coverage s hs hls
  obtain ⟨b, hb, u, hu⟩ := representative_coverage t ht hlt
  have hk : orbitKey column a = orbitKey column b := by
    have hf := congrArg (fun x => (minRotation x).toNat) he
    rw [hr, hu, syndrome_act column eqv, syndrome_act column eqv,
      minRotation_invariant, minRotation_invariant] at hf
    exact hf
  have hab := representatives_keys_unique column h a b ha hb hk
  subst b
  rw [hr, hu]
  apply orbit_local_injective column eqv h a ha r u
  simpa only [hr, hu] using he

theorem orbit_full_key_nodup (column : Coord → Nat)
    (eqv : Equivariant (fun q => BitVec.ofNat 39 (column q)))
    (h : checkOrbit (fun q => BitVec.ofNat 39 (column q)) = true) :
    (half4Keys ((List.finRange 156).map column)).Nodup := by
  rw [← half4Supports_map_syndrome]
  apply List.pairwise_map.mpr
  have hc : (List.finRange 156).Nodup := by decide
  apply (half4Supports_nodup (List.finRange 156) hc).imp_of_mem
  intro a b ha hb hne he
  obtain ⟨hasub, halen⟩ := half4Supports_mem (List.finRange 156) a ha
  obtain ⟨hbsub, hblen⟩ := half4Supports_mem (List.finRange 156) b hb
  have hasort : a.Pairwise (· ≤ ·) := List.Pairwise.sublist hasub (by decide)
  have hbsort : b.Pairwise (· ≤ ·) := List.Pairwise.sublist hbsub (by decide)
  have hbits : syndrome (fun q => BitVec.ofNat 39 (column q)) a =
      syndrome (fun q => BitVec.ofNat 39 (column q)) b := by
    rw [syndrome_ofNat, syndrome_ofNat, he]
  have hab := checkOrbit_injective (fun q => BitVec.ofNat 39 (column q)) eqv h
    ⟨a, hasort⟩ ⟨b, hbsort⟩ (hasub.nodup hc) (hbsub.nodup hc) halen hblen hbits
  exact hne (congrArg Subtype.val hab)

theorem orbit_checkHalf4 (bases : List Nat) (column : Coord → Nat)
    (binding : (List.finRange 156).map column = columns bases)
    (eqv : Equivariant (fun q => BitVec.ofNat 39 (column q)))
    (h : checkOrbit (fun q => BitVec.ofNat 39 (column q)) = true) :
    checkHalf4 bases = true := by
  apply checkHalf4_complete
  rw [← binding]
  exact orbit_full_key_nodup column eqv h

end QEC663.Orbit
