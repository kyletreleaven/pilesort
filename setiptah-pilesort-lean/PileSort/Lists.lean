/-
  General-purpose list lemmas not available in core Lean 4.
-/

open List

/-- List.finRange n is Nodup: distinct positions map to distinct Fin n elements. -/
theorem nodup_finRange (n : Nat) : (List.finRange n).Nodup := by
  simp [List.Nodup, List.pairwise_iff_getElem, Fin.ext_iff, Nat.ne_of_lt]
  omega

/-- filterMap on a Nodup list is Nodup when the function is injective on Some values. -/
theorem List.Nodup.filterMap {α β : Type} {f : α → Option β} {l : List α}
    (hnd : l.Nodup)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, ∀ x, f a = some x → f b = some x → a = b) :
    (l.filterMap f).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hnd_tl := hnd.of_cons
    have hinj_tl : ∀ a ∈ tl, ∀ b ∈ tl, ∀ x, f a = some x → f b = some x → a = b :=
      fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    simp only [List.filterMap_cons]
    cases hf : f hd with
    | none => exact ih hnd_tl hinj_tl
    | some v =>
      refine List.nodup_cons.mpr ⟨?_, ih hnd_tl hinj_tl⟩
      intro hmem
      obtain ⟨a, ha_mem, hfa⟩ := List.mem_filterMap.mp hmem
      have heq : hd = a :=
        hinj hd (List.mem_cons_self _ _) a (List.mem_cons_of_mem _ ha_mem) v hf hfa
      exact (List.nodup_cons.mp hnd).1 (heq ▸ ha_mem)

/-- flatMap respects pointwise equality of functions. -/
theorem List.flatMap_congr {α β : Type} {f g : α → List β} {l : List α}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self a t), ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-- Elements in take k of finRange n have value < k. -/
theorem val_lt_of_mem_take_finRange {n k : Nat} {p : Fin n}
    (h : p ∈ (List.finRange n).take k) : p.val < k := by
  rw [List.mem_take_iff_getElem] at h
  obtain ⟨i, hi, hieq⟩ := h
  simp only [List.length_finRange] at hi
  have : p.val = i := by
    have := congrArg Fin.val hieq
    simp [List.getElem_finRange] at this
    omega
  omega

/-- Elements in drop k of finRange n have value ≥ k. -/
theorem val_ge_of_mem_drop_finRange {n k : Nat} {p : Fin n}
    (h : p ∈ (List.finRange n).drop k) : k ≤ p.val := by
  rw [List.mem_drop_iff_getElem] at h
  obtain ⟨i, hi, hieq⟩ := h
  have : p.val = k + i := by
    have := congrArg Fin.val hieq
    simp [List.getElem_finRange] at this
    omega
  omega

/-- finRange m splits at position j: take ++ [j] ++ drop. -/
theorem finRange_split {m : Nat} (j : Fin m) :
    List.finRange m =
      (List.finRange m).take j.val ++ [j] ++ (List.finRange m).drop (j.val + 1) := by
  have hlen : j.val < (List.finRange m).length := by simp
  have hdrop : (List.finRange m).drop j.val = j :: (List.finRange m).drop (j.val + 1) :=
    (List.drop_eq_getElem_cons hlen).trans (by simp [List.getElem_finRange, Fin.ext_iff])
  rw [List.append_assoc, List.singleton_append, ← hdrop]
  exact (List.take_append_drop j.val (List.finRange m)).symm

private theorem finRange_flatMap_split {α : Type} {m : Nat} (j : Fin m) (f : Fin m → List α) :
    (List.finRange m).flatMap f =
      ((List.finRange m).take j.val).flatMap f ++ f j ++
      ((List.finRange m).drop (j.val + 1)).flatMap f := by
  conv => lhs; rw [finRange_split j]
  simp [List.flatMap_append, List.flatMap_cons, List.flatMap_nil]

private theorem flatMap_if_of_ne {α : Type} {m : Nat} (a : α) (f : α → Fin m)
    (l : List (Fin m)) (hne : ∀ p ∈ l, f a ≠ p) (t : List α) :
    l.flatMap (fun p => if decide (f a = p) = true
                        then a :: t.filter (fun c => decide (f c = p))
                        else t.filter (fun c => decide (f c = p))) =
    l.flatMap (fun p => t.filter (fun c => decide (f c = p))) :=
  List.flatMap_congr fun p hp => by simp [decide_eq_false_iff_not.mpr (hne p hp)]

/-- Cons step: distributing (a :: t) over buckets permutes to a prepended. -/
private theorem flatMap_filter_cons_eq {α : Type} {m : Nat} (a : α) (t : List α)
    (f : α → Fin m) :
    let tf := fun p : Fin m => t.filter (fun c => decide (f c = p))
    (List.finRange m).flatMap (fun p => if decide (f a = p) = true then a :: tf p else tf p) =
    ((List.finRange m).take (f a).val).flatMap tf ++
      a :: (tf (f a) ++ ((List.finRange m).drop ((f a).val + 1)).flatMap tf) := by
  intro tf
  rw [finRange_flatMap_split (f a) (fun p => if decide (f a = p) = true then a :: tf p else tf p)]
  rw [flatMap_if_of_ne a f _
        (fun p hp h => absurd (congrArg Fin.val h)
          (Nat.ne_of_gt (val_lt_of_mem_take_finRange hp))) t]
  rw [flatMap_if_of_ne a f _
        (fun p hp h => absurd (congrArg Fin.val h)
          (Nat.ne_of_lt (Nat.lt_of_succ_le (val_ge_of_mem_drop_finRange hp)))) t]
  rw [if_pos (decide_eq_true rfl)]
  simp only [show tf = fun p : Fin m => t.filter (fun c => decide (f c = p)) from rfl]
  simp [List.append_assoc, List.cons_append]

theorem flatMap_filter_cons {α : Type} {m : Nat} (a : α) (t : List α) (f : α → Fin m) :
    (List.finRange m).flatMap (fun p => (a :: t).filter (fun c => decide (f c = p))) ~
    a :: (List.finRange m).flatMap (fun p => t.filter (fun c => decide (f c = p))) := by
  simp only [List.filter_cons]
  rw [flatMap_filter_cons_eq,
      finRange_flatMap_split (f a) (fun p => t.filter (fun c => decide (f c = p))),
      List.append_assoc]
  exact List.perm_middle

/-- Partitioning a list into piles by a function and flatMapping is a permutation of the
    original list. -/
theorem flatMap_filter_perm {α : Type} {m : Nat} (l : List α) (f : α → Fin m) :
    List.Perm ((List.finRange m).flatMap (fun p => l.filter (fun c => decide (f c = p)))) l := by
  induction l with
  | nil => simp
  | cons a t ih => exact (flatMap_filter_cons a t f).trans (ih.cons a)
