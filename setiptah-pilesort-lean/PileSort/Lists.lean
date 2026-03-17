/-
  General-purpose list lemmas not available in core Lean 4.
-/

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
