import Std

namespace QEC663.Architecture

/-- A finite table with a nodup syndrome list is injective on its members. -/
theorem map_nodup_injective_on {S T : Type} (f : S → T) :
    ∀ xs : List S, (xs.map f).Nodup →
    ∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b
  | [], _, _, ha, _, _, _ => by simp at ha
  | x :: xs, hn, a, ha, b, hb, hab => by
    have hn' : (f x :: xs.map f).Nodup := hn
    have hhead := (List.nodup_cons.mp hn').1
    have htail := (List.nodup_cons.mp hn').2
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      rcases List.mem_cons.mp hb with hb | hb
      · exact hb.symm
      · have hm : f x ∈ xs.map f := List.mem_map.mpr ⟨b, hb, hab.symm⟩
        exact False.elim (hhead hm)
    · rcases List.mem_cons.mp hb with hb | hb
      · subst b
        have hm : f x ∈ xs.map f := List.mem_map.mpr ⟨a, ha, hab⟩
        exact False.elim (hhead hm)
      · exact map_nodup_injective_on f xs htail a ha b hb hab

/-- Explicit coverage upgrades table injectivity to the entire support domain. -/
theorem table_injective_of_coverage {S T : Type}
    (f : S → T) (table : List S) (admissible : S → Prop)
    (coverage : ∀ s, admissible s → s ∈ table)
    (table_checked : (table.map f).Nodup)
    (s t : S) (hs : admissible s) (ht : admissible t)
    (he : f s = f t) : s = t :=
  map_nodup_injective_on f table table_checked s (coverage s hs)
    t (coverage t ht) he

/-- A duplicate concatenation can be nodup only when empty. -/
theorem empty_of_self_append_nodup {Q : Type} (s : List Q)
    (h : (s ++ s).Nodup) : s = [] := by
  cases s with
  | nil => rfl
  | cons x xs =>
    simp only [List.cons_append] at h
    have hn := (List.nodup_cons.mp h).1
    have hm : x ∈ xs ++ (x :: xs) := by simp
    exact False.elim (hn hm)

/-- Half-support injectivity plus odd-column augmentation gives minimum ten.
The support is a nodup list; admissibility may impose sorted order or bounds.
The only table premise is injectivity, not the desired minimum-distance claim. -/
theorem half4_classical_kernel_min10
    {Q T : Type} (syndrome : List Q → T) (zero : T)
    (admissible : List Q → Prop)
    (take_admissible : ∀ s, admissible s → admissible (s.take 4))
    (drop_admissible : ∀ s, admissible s → admissible (s.drop 4))
    (append_zero : ∀ a b, syndrome (a ++ b) = zero ↔ syndrome a = syndrome b)
    (zero_even : ∀ s, admissible s → syndrome s = zero → s.length % 2 = 0)
    (half4_injective : ∀ a b, admissible a → admissible b →
      a.length ≤ 4 → b.length ≤ 4 → syndrome a = syndrome b → a = b)
    (s : List Q) (hs : admissible s) (hn : s.Nodup)
    (hker : syndrome s = zero) (hne : s ≠ []) :
    10 ≤ s.length := by
  by_cases hlarge : 10 ≤ s.length
  · exact hlarge
  exfalso
  have heven := zero_even s hs hker
  have hlen : s.length ≤ 8 := by omega
  have htake : (s.take 4).length ≤ 4 := by simp; omega
  have hdrop : (s.drop 4).length ≤ 4 := by simp; omega
  have hsyn : syndrome (s.take 4) = syndrome (s.drop 4) := by
    apply (append_zero (s.take 4) (s.drop 4)).mp
    simpa only [List.take_append_drop] using hker
  have heq := half4_injective (s.take 4) (s.drop 4)
    (take_admissible s hs) (drop_admissible s hs) htake hdrop hsyn
  have hsplit : s = s.take 4 ++ s.take 4 := by
    calc
      s = s.take 4 ++ s.drop 4 := (List.take_append_drop 4 s).symm
      _ = s.take 4 ++ s.take 4 := by rw [← heq]
  have hn' : (s.take 4 ++ s.take 4).Nodup := hsplit ▸ hn
  have hempty := empty_of_self_append_nodup (s.take 4) hn'
  apply hne
  simpa only [hempty, List.nil_append] using hsplit

end QEC663.Architecture
