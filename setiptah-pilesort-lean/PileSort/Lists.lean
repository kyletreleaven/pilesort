/-
  General-purpose list lemmas not available in core Lean 4.

  ## Proof plan for shuffleRound_order (bottom-up)

  ### Lists.lean (this file)

  1. `list_split_at` — for `a ∈ l`, splits `l = l.take (indexOf a l) ++ [a] ++ l.drop (indexOf a l + 1)`.
     Assembles from `take_append_drop`, `drop_eq_getElem_cons`, `getElem_indexOf`.

  2. `indexOf_append_not_mem` — if `a ∉ l₁` then `(l₁ ++ l₂).indexOf a = l₁.length + l₂.indexOf a`.
     Short induction on `l₁`.
     NOTE: may not be needed as a standalone — since we have nodup throughout, `a ∉ prefix` and
     `a ∉ suffix` follow immediately from the split, so this may be inlineable at each use site.

  3. `indexOf_filter_lt` — for nodup `l` with `a, b ∈ l.filter f`:
       `(l.filter f).indexOf a < (l.filter f).indexOf b ↔ l.indexOf a < l.indexOf b`
     Uses 1 (split at a, bootstrap to split at b), `List.filter_append`, and nodup to
     conclude `a ∉ prefix`/`suffix` (possibly inlining 2).

  4. `indexOf_reverse_lt` — for nodup `l` with `a, b ∈ l`:
       `l.reverse.indexOf a < l.reverse.indexOf b ↔ l.indexOf b < l.indexOf a`
     Uses 1 and nodup on the reversed decomposition (possibly inlining 2).

  5. `indexOf_flatMap_order` — for a nodup `(finRange m).flatMap piles` with `s ∈ piles ps`, `t ∈ piles pt`:
       `indexOf s (...) < indexOf t (...) ↔ ps < pt ∨ (ps = pt ∧ (piles ps).indexOf s < (piles ps).indexOf t)`
     Uses 2 and `finRange_flatMap_split`.

  ### PileShuffle.lean

  6. `shuffleSeq_order` — list-level version of shuffleRound_order:
       `(shuffleSeq l types assign).indexOf s < (...).indexOf t ↔ ...`
     Applies 5, then 3 (Q case) and 4 (S case) for within-pile comparison.
     Connects `l.indexOf s` to `d.posOf s` via `indexOf_getElem` + `left_inv` (inlined).

  7. `shuffleRound_order` — lifts 6 to Deck by unfolding `fromDeckSeq.posOf`.
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

/-- The i-th element of (finRange m).map f is f i. -/
theorem finRange_map_get {α : Type} {m : Nat} (f : Fin m → α) (i : Fin m) :
    ((List.finRange m).map f).get ⟨i.val, by simp⟩ = f i := by
  simp [List.getElem_map, List.getElem_finRange, Fin.ext_iff]

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

/-- p.val < k implies p is in the first k elements of finRange n. -/
private theorem mem_take_finRange_of_lt {n k : Nat} {p : Fin n} (h : p.val < k) :
    p ∈ (List.finRange n).take k := by
  rw [List.mem_take_iff_getElem]
  exact ⟨p.val, by simp; omega, by simp [List.getElem_finRange, Fin.ext_iff]⟩

/-- indexOf in a concatenation when a is in the prefix. -/
theorem indexOf_append_of_mem {α : Type} [DecidableEq α] {a : α} {l₁ l₂ : List α}
    (h : a ∈ l₁) : (l₁ ++ l₂).indexOf a = l₁.indexOf a := by
  induction l₁ with
  | nil => exact absurd h (List.not_mem_nil _)
  | cons x xs ih =>
    by_cases hax : x = a
    · subst hax; simp [List.indexOf_cons]
    · have h' : a ∈ xs := (List.mem_cons.mp h).resolve_left (Ne.symm hax)
      simp only [List.cons_append, List.indexOf_cons,
                 show (x == a) = false from by simp [hax], cond_false]
      exact congrArg (· + 1) (ih h')

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

/-- indexOf is strictly less than the list length when the element is a member. -/
theorem indexOf_lt_length {α : Type} [DecidableEq α] {a : α} {l : List α} (hmem : a ∈ l) :
    l.indexOf a < l.length := by
  induction l with
  | nil => exact absurd hmem (List.not_mem_nil _)
  | cons x xs ih =>
    simp only [List.length_cons]
    by_cases hax : x = a
    · simp [List.indexOf_cons, hax]
    · have hmem' : a ∈ xs := (List.mem_cons.mp hmem).resolve_left (Ne.symm hax)
      simp only [List.indexOf_cons, show (x == a) = false from by simp [hax], cond_false]
      exact Nat.succ_lt_succ (ih hmem')

/-- The element at its own indexOf is itself (no Nodup required). -/
theorem getElem_indexOf {α : Type} [DecidableEq α] {a : α} {l : List α} (hmem : a ∈ l) :
    l[l.indexOf a]'(indexOf_lt_length hmem) = a := by
  induction l with
  | nil => exact absurd hmem (List.not_mem_nil _)
  | cons x xs ih =>
    by_cases hax : x = a
    · subst hax; simp [List.indexOf_cons]
    · have hmem' : a ∈ xs := (List.mem_cons.mp hmem).resolve_left (Ne.symm hax)
      simp only [List.indexOf_cons, show (x == a) = false from by simp [hax], cond_false,
                 List.getElem_cons_succ]
      exact ih hmem'

/-- Split a list at the first occurrence of a: l = prefix ++ [a] ++ suffix. -/
-- if a ∈ l.take k then indexOf a l < k
private theorem indexOf_lt_of_mem_take {α : Type} [DecidableEq α] {a : α} {l : List α} {k : Nat}
    (h : a ∈ l.take k) : l.indexOf a < k := by
  induction l generalizing k with
  | nil => simp at h
  | cons x xs ih =>
    cases k with
    | zero => simp at h
    | succ k =>
      simp only [List.take_succ_cons] at h
      simp only [List.indexOf_cons]
      by_cases hax : x = a
      · simp [hax]
      · have h' : a ∈ xs.take k := (List.mem_cons.mp h).resolve_left (Ne.symm hax)
        simp only [show (x == a) = false from by simp [hax], cond_false]
        exact Nat.succ_lt_succ (ih h')

-- a ∉ l.take (indexOf a l)
private theorem not_mem_take_indexOf {α : Type} [DecidableEq α] {a : α} {l : List α} :
    a ∉ l.take (l.indexOf a) :=
  fun h => absurd (indexOf_lt_of_mem_take h) (Nat.lt_irrefl _)

theorem list_split_at {α : Type} [DecidableEq α] {l : List α} {a : α} (h : a ∈ l) :
    l = l.take (l.indexOf a) ++ [a] ++ l.drop (l.indexOf a + 1) := by
  have hlt : l.indexOf a < l.length := indexOf_lt_length h
  have hdrop : l.drop (l.indexOf a) = a :: l.drop (l.indexOf a + 1) := by
    rw [List.drop_eq_getElem_cons hlt, getElem_indexOf h]
  calc l = l.take (l.indexOf a) ++ l.drop (l.indexOf a) := (List.take_append_drop _ _).symm
    _ = l.take (l.indexOf a) ++ (a :: l.drop (l.indexOf a + 1)) := by rw [hdrop]
    _ = l.take (l.indexOf a) ++ [a] ++ l.drop (l.indexOf a + 1) := by simp [List.append_assoc]

/-- Two-element split: given indexOf a l < indexOf b l, decompose l into pre ++ [a] ++ mid ++ [b] ++ suf,
    with non-membership witnesses. -/
theorem list_split_two {α : Type} [DecidableEq α] {l : List α} {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hlt : l.indexOf a < l.indexOf b) :
    ∃ pre mid suf : List α,
      l = pre ++ [a] ++ mid ++ [b] ++ suf ∧
      a ∉ pre ∧ b ∉ pre ∧ a ≠ b ∧ b ∉ mid := by
  have hab : a ≠ b := fun h => absurd (h ▸ hlt) (Nat.lt_irrefl _)
  have hb_not_pre : b ∉ l.take (l.indexOf a) := fun h =>
    absurd (indexOf_lt_of_mem_take h) (Nat.not_lt.mpr (Nat.le_of_lt hlt))
  have hl_split_a := list_split_at ha
  have hb_in_suffix : b ∈ l.drop (l.indexOf a + 1) := by
    have : b ∈ l.take (l.indexOf a) ++ [a] ++ l.drop (l.indexOf a + 1) := hl_split_a ▸ hb
    simp [List.mem_append, hb_not_pre, hab.symm] at this
    exact this
  have hs_split_b := list_split_at hb_in_suffix
  exact ⟨l.take (l.indexOf a),
         (l.drop (l.indexOf a + 1)).take ((l.drop (l.indexOf a + 1)).indexOf b),
         (l.drop (l.indexOf a + 1)).drop ((l.drop (l.indexOf a + 1)).indexOf b + 1),
         by conv => lhs; rw [hl_split_a, hs_split_b]
            simp [List.append_assoc],
         not_mem_take_indexOf,
         hb_not_pre,
         hab,
         not_mem_take_indexOf⟩

-- indexOf in a concatenation when a is not in the prefix
theorem indexOf_append_not_mem {α : Type} [DecidableEq α] {a : α} (l₁ l₂ : List α)
    (h : a ∉ l₁) : (l₁ ++ l₂).indexOf a = l₁.length + l₂.indexOf a := by
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
    have hxa : x ≠ a := fun heq => h (heq ▸ List.mem_cons_self x xs)
    have h' : a ∉ xs := fun hmem => h (List.mem_cons_of_mem x hmem)
    simp only [List.cons_append, List.indexOf_cons,
               show (x == a) = false from by simp [hxa], cond_false,
               List.length_cons, ih h']
    omega

-- helper: given split with x before y (x ∉ pre, y ∉ pre ++ [x] ++ mid), indexOf x = pre.length
private theorem indexOf_split_fst {α : Type} [DecidableEq α] {x : α} {pre rest : List α}
    (hx : x ∉ pre) : (pre ++ x :: rest).indexOf x = pre.length := by
  simp [indexOf_append_not_mem _ _ hx, List.indexOf_cons]

private theorem indexOf_split_snd {α : Type} [DecidableEq α] {x y : α} {pre mid suf : List α}
    (hy_pre : y ∉ pre) (hyx : y ≠ x) (hy_mid : y ∉ mid) :
    (pre ++ [x] ++ mid ++ [y] ++ suf).indexOf y = pre.length + 1 + mid.length := by
  have hpxm : y ∉ pre ++ [x] ++ mid := by simp [List.mem_append, hy_pre, hyx, hy_mid]
  rw [show pre ++ [x] ++ mid ++ [y] ++ suf = (pre ++ [x] ++ mid) ++ y :: suf by
        simp [List.append_assoc],
      indexOf_append_not_mem _ _ hpxm]
  simp [List.indexOf_cons, List.length_append]
  omega

-- indexOf of the fst pivot is less than indexOf of the snd pivot in a split list.
private theorem indexOf_fst_lt_snd {α : Type} [DecidableEq α] {x y : α} {A B C : List α}
    (hxA : x ∉ A) (hyA : y ∉ A) (hyx : y ≠ x) (hyB : y ∉ B) :
    (A ++ x :: B ++ y :: C).indexOf x < (A ++ x :: B ++ y :: C).indexOf y := by
  have hxidx : (A ++ x :: B ++ y :: C).indexOf x = A.length := by
    rw [show A ++ x :: B ++ y :: C = A ++ x :: (B ++ y :: C) from by
        simp [List.cons_append, List.append_assoc]]
    exact indexOf_split_fst hxA
  have hy_nmem : y ∉ A ++ x :: B := by simp [List.mem_append, hyA, hyx, hyB]
  have hyidx : (A ++ x :: B ++ y :: C).indexOf y = A.length + 1 + B.length := by
    rw [indexOf_append_not_mem _ _ hy_nmem]
    simp [List.indexOf_cons, List.length_append]; omega
  omega

theorem indexOf_filter_lt {α : Type} [DecidableEq α] {f : α → Bool} {l : List α}
    {a b : α} (ha : a ∈ l.filter f) (hb : b ∈ l.filter f) :
    (l.filter f).indexOf a < (l.filter f).indexOf b ↔ l.indexOf a < l.indexOf b := by
  have ha_l : a ∈ l := (List.mem_filter.mp ha).1
  have hb_l : b ∈ l := (List.mem_filter.mp hb).1
  have hfa : f a = true := (List.mem_filter.mp ha).2
  have hfb : f b = true := (List.mem_filter.mp hb).2
  constructor
  · intro hlt_flt
    rcases Nat.lt_trichotomy (l.indexOf a) (l.indexOf b) with h | h | h
    · exact h
    · -- indexOf a = indexOf b → a = b → contradiction
      have hab : a = b := by
        have h1 := getElem_indexOf ha_l
        simp only [h] at h1
        exact h1.symm.trans (getElem_indexOf hb_l)
      subst hab; exact absurd hlt_flt (Nat.lt_irrefl _)
    · -- l.indexOf b < l.indexOf a: split with b before a, filter gives b before a, contradiction
      obtain ⟨pre, mid, suf, hl_eq, hb_pre, ha_pre, hba, ha_mid⟩ := list_split_two hb_l ha_l h
      have hflt_eq : l.filter f = pre.filter f ++ b :: mid.filter f ++ a :: suf.filter f := by
        rw [hl_eq]; simp [List.filter_append, List.filter_cons, hfb, hfa]
      have hb_pref : b ∉ pre.filter f := fun hmem => hb_pre (List.mem_filter.mp hmem).1
      have ha_pref : a ∉ pre.filter f := fun hmem => ha_pre (List.mem_filter.mp hmem).1
      have ha_midf : a ∉ mid.filter f := fun hmem => ha_mid (List.mem_filter.mp hmem).1
      have hord : (pre.filter f ++ b :: mid.filter f ++ a :: suf.filter f).indexOf b <
                  (pre.filter f ++ b :: mid.filter f ++ a :: suf.filter f).indexOf a :=
        indexOf_fst_lt_snd hb_pref ha_pref hba.symm ha_midf
      rw [← hflt_eq] at hord; omega
  · intro hlt
    obtain ⟨pre, mid, suf, hl_eq, ha_pre, hb_pre, hab, hb_mid⟩ := list_split_two ha_l hb_l hlt
    have hflt_eq : l.filter f = pre.filter f ++ a :: mid.filter f ++ b :: suf.filter f := by
      rw [hl_eq]; simp [List.filter_append, List.filter_cons, hfa, hfb]
    have ha_pref : a ∉ pre.filter f := fun hmem => ha_pre (List.mem_filter.mp hmem).1
    have hb_pref : b ∉ pre.filter f := fun hmem => hb_pre (List.mem_filter.mp hmem).1
    have hb_midf : b ∉ mid.filter f := fun hmem => hb_mid (List.mem_filter.mp hmem).1
    have hord : (pre.filter f ++ a :: mid.filter f ++ b :: suf.filter f).indexOf a <
                (pre.filter f ++ a :: mid.filter f ++ b :: suf.filter f).indexOf b :=
      indexOf_fst_lt_snd ha_pref hb_pref hab.symm hb_midf
    rwa [← hflt_eq] at hord

theorem flatMap_filter_cons {α : Type} {m : Nat} (a : α) (t : List α) (f : α → Fin m) :
    (List.finRange m).flatMap (fun p => (a :: t).filter (fun c => decide (f c = p))) ~
    a :: (List.finRange m).flatMap (fun p => t.filter (fun c => decide (f c = p))) := by
  simp only [List.filter_cons]
  rw [flatMap_filter_cons_eq,
      finRange_flatMap_split (f a) (fun p => t.filter (fun c => decide (f c = p))),
      List.append_assoc]
  exact List.perm_middle

theorem indexOf_reverse_eq {α : Type} [DecidableEq α] {l : List α} {a : α}
    (hnd : l.Nodup) (ha : a ∈ l) :
    l.reverse.indexOf a = l.length - l.indexOf a - 1 := by
  have hlt := indexOf_lt_length ha
  -- a ∉ l.drop (indexOf a + 1): drop is nodup, equals a :: suf, so a ∉ suf
  have hdrop_nd : (l.drop (l.indexOf a)).Nodup :=
    hnd.sublist (List.drop_sublist _ l)
  have hdrop_eq : l.drop (l.indexOf a) = a :: l.drop (l.indexOf a + 1) :=
    (List.drop_eq_getElem_cons hlt).trans (by simp [getElem_indexOf ha])
  have ha_suf : a ∉ l.drop (l.indexOf a + 1) :=
    (List.nodup_cons.mp (hdrop_eq ▸ hdrop_nd)).1
  -- reverse of the split: suf.reverse ++ [a] ++ pre.reverse
  have hrev : l.reverse = (l.drop (l.indexOf a + 1)).reverse ++ a ::
                           (l.take (l.indexOf a)).reverse := by
    conv => lhs; rw [list_split_at ha]
    simp [List.reverse_append]
  rw [hrev, indexOf_split_fst (fun h => ha_suf (List.mem_reverse.mp h))]
  simp only [List.length_reverse, List.length_drop]
  omega

theorem indexOf_reverse_lt {α : Type} [DecidableEq α] {l : List α} {a b : α}
    (hnd : l.Nodup) (ha : a ∈ l) (hb : b ∈ l) :
    l.reverse.indexOf a < l.reverse.indexOf b ↔ l.indexOf b < l.indexOf a := by
  have ha_lt := indexOf_lt_length ha
  have hb_lt := indexOf_lt_length hb
  rw [indexOf_reverse_eq hnd ha, indexOf_reverse_eq hnd hb]
  constructor <;> intro h <;> omega

/-- flatMap respects pointwise permutation of the mapped function. -/
theorem List.flatMap_perm_congr {α β : Type} {f g : α → List β} {l : List α}
    (h : ∀ a ∈ l, f a ~ g a) : l.flatMap f ~ l.flatMap g := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons]
    exact ((h a (List.mem_cons_self a t)).append_right _).trans
      (((ih (fun b hb => h b (List.mem_cons_of_mem a hb)))).append_left _)

/-- Partitioning a list into piles by a function and flatMapping is a permutation of the
    original list. -/
theorem flatMap_filter_perm {α : Type} {m : Nat} (l : List α) (f : α → Fin m) :
    List.Perm ((List.finRange m).flatMap (fun p => l.filter (fun c => decide (f c = p)))) l := by
  induction l with
  | nil => simp
  | cons a t ih => exact (flatMap_filter_cons a t f).trans (ih.cons a)

/-- Order in a flatMap: for a nodup flatMap, indexOf s < indexOf t iff
    the pile index of s is smaller, or the piles are equal and s comes before t within the pile. -/
theorem indexOf_flatMap_order {n m : Nat} (piles : Fin m → List (Fin n))
    (hnd : ((List.finRange m).flatMap piles).Nodup)
    {s t : Fin n} {ps pt : Fin m}
    (hs : s ∈ piles ps) (ht : t ∈ piles pt) :
    ((List.finRange m).flatMap piles).indexOf s <
    ((List.finRange m).flatMap piles).indexOf t ↔
      ps < pt ∨ (ps = pt ∧ (piles ps).indexOf s < (piles ps).indexOf t) := by
  sorry
