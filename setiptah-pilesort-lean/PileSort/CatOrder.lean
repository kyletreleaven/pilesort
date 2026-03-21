/-
  Ordering lemmas for elements in a nodup concatenation of lists.

  Given a list of lists whose flatten is Nodup:
  1. If a ∈ lists[i] and b ∈ lists[j] with i < j, then a precedes b in the flatten.
  2. If a, b ∈ lists[i], their order in the flatten equals their order within lists[i].
-/
import PileSort.Permutations

private theorem nodup_append_not_mem {α : Type} {l₁ l₂ : List α}
    (h : (l₁ ++ l₂).Nodup) {a : α} (h₁ : a ∈ l₁) : a ∉ l₂ := by
  induction l₁ with
  | nil => exact absurd h₁ (List.not_mem_nil _)
  | cons hd tl ih =>
    simp only [List.cons_append, List.nodup_cons] at h
    cases h₁ with
    | head => exact fun h₂ => h.1 (List.mem_append_right tl h₂)
    | tail _ htl => exact ih h.2 htl

/-- In a Nodup flatten, indexOf a (where a ∈ lists[i]) equals the flattened prefix
    length plus indexOf a within lists[i] alone. -/
private theorem indexOf_flatten_eq {α : Type} [DecidableEq α] (lists : List (List α))
    (hnd : lists.flatten.Nodup) (i : Fin lists.length) {a : α} (ha : a ∈ lists.get i) :
    lists.flatten.indexOf a = (lists.take i.val).flatten.length + (lists.get i).indexOf a := by
  induction lists with
  | nil => exact i.elim0
  | cons hd tl ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.zero_eta, List.get_cons_zero] at ha
      simp [List.flatten_cons, indexOf_append_of_mem ha]
    | succ k =>
      have hnd' : (hd ++ tl.flatten).Nodup := by simpa [List.flatten_cons] using hnd
      simp only [Fin.val_succ, List.take_succ_cons, List.get_eq_getElem,
                 List.getElem_cons_succ, List.flatten_cons]
      have ha' : a ∈ tl.get k := by rwa [List.get_eq_getElem]
      have ha_tl : a ∈ tl.flatten :=
        List.mem_flatten.mpr ⟨tl.get k, List.get_mem tl k, ha'⟩
      have hnd_tl : tl.flatten.Nodup :=
        hnd'.sublist (List.sublist_append_right hd _)
      have ha_nhd : a ∉ hd := fun h => absurd ha_tl (nodup_append_not_mem hnd' h)
      rw [indexOf_append_not_mem _ _ ha_nhd, ← List.get_eq_getElem, ih hnd_tl k ha']
      simp [List.length_append]; omega

/-- If the flatten of a list of lists is Nodup, and a ∈ lists[i], b ∈ lists[j] with i < j,
    then a precedes b in the flatten. -/
theorem indexOf_flatten_of_lt {α : Type} [DecidableEq α] (lists : List (List α))
    (hnd : lists.flatten.Nodup) {i j : Fin lists.length} (hij : i < j)
    {a b : α} (ha : a ∈ lists.get i) (hb : b ∈ lists.get j) :
    lists.flatten.indexOf a < lists.flatten.indexOf b := by
  -- Split the flatten at j: everything before j, then everything from j onward
  have hflat : lists.flatten = (lists.take j.val).flatten ++ (lists.drop j.val).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  -- a ∈ lists[i] with i < j, so lists[i] ∈ lists.take j, hence a ∈ (lists.take j).flatten
  have ha_take : a ∈ (lists.take j.val).flatten := by
    apply List.mem_flatten.mpr
    refine ⟨lists.get i, ?_, ha⟩
    have hilen : i.val < (lists.take j.val).length := by
      simp only [List.length_take]; omega
    have heq : (lists.take j.val)[i.val]'hilen = lists.get i := by
      simp [List.getElem_take, List.get_eq_getElem]
    exact heq ▸ List.getElem_mem hilen
  -- b ∈ lists[j], and lists.drop j starts with lists[j], so b ∈ (lists.drop j).flatten
  have hb_drop : b ∈ (lists.drop j.val).flatten := by
    apply List.mem_flatten.mpr
    refine ⟨lists.get j, ?_, hb⟩
    have hdrop : lists.drop j.val = lists.get j :: lists.drop (j.val + 1) := by
      rw [List.drop_eq_getElem_cons j.isLt]; simp [List.get_eq_getElem]
    rw [hdrop]; exact List.mem_cons_self _ _
  -- Nodup of the full flatten means b cannot appear in both halves
  have hb_not_take : b ∉ (lists.take j.val).flatten := fun h =>
    absurd hb_drop (nodup_append_not_mem (hflat ▸ hnd) h)
  -- indexOf a lands in the left half, indexOf b in the right half
  rw [hflat, indexOf_append_of_mem ha_take, indexOf_append_not_mem _ _ hb_not_take]
  have := indexOf_lt_length ha_take
  omega

/-- If the flatten of a list of lists is Nodup, and a, b ∈ lists[i],
    their order in the flatten equals their order within lists[i]. -/
theorem indexOf_flatten_same {α : Type} [DecidableEq α] (lists : List (List α))
    (hnd : lists.flatten.Nodup) {i : Fin lists.length}
    {a b : α} (ha : a ∈ lists.get i) (hb : b ∈ lists.get i) :
    lists.flatten.indexOf a < lists.flatten.indexOf b ↔
    (lists.get i).indexOf a < (lists.get i).indexOf b := by
  rw [indexOf_flatten_eq lists hnd i ha, indexOf_flatten_eq lists hnd i hb]
  omega

/-- Nat-index corollary of `indexOf_flatten_of_lt`. -/
theorem indexOf_flatten_of_lt_val {α : Type} [DecidableEq α] (lists : List (List α))
    (hnd : lists.flatten.Nodup) {i j : Nat} (hi : i < lists.length) (hj : j < lists.length)
    (hij : i < j) {a b : α} (ha : a ∈ lists[i]'hi) (hb : b ∈ lists[j]'hj) :
    lists.flatten.indexOf a < lists.flatten.indexOf b :=
  indexOf_flatten_of_lt lists hnd hij ha hb

/-- Nat-index corollary of `indexOf_flatten_same`. -/
theorem indexOf_flatten_same_val {α : Type} [DecidableEq α] (lists : List (List α))
    (hnd : lists.flatten.Nodup) {i : Nat} (hi : i < lists.length)
    {a b : α} (ha : a ∈ lists[i]'hi) (hb : b ∈ lists[i]'hi) :
    lists.flatten.indexOf a < lists.flatten.indexOf b ↔
    (lists[i]'hi).indexOf a < (lists[i]'hi).indexOf b :=
  indexOf_flatten_same lists hnd ha hb
