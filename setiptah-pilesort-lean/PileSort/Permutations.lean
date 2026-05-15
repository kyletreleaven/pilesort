import PileSort.Lists

/-!
  Technical lemmas about bijections of `Fin n`.

  These underpin `Deck.fromDeckSeq` and `Deck.fromCardPositions`.
  The core tool is a `Nodup` list of `Fin n` with length `n`, which
  represents a bijection (either direction).

  Key results:
  - `indexOf_lt_length` — `a ∈ l → l.indexOf a < l.length`
  - `getElem_indexOf` — `a ∈ l → l[l.indexOf a] = a` (no Nodup required)
  - `indexOf_getElem` — `l.Nodup → l.indexOf l[k] = k`
  - `Fin.mem_of_nodup_length` — a Nodup list of `Fin n` with length `n` contains every element
  - `Fin.invOf` — computable inverse of an injective `Fin n → Fin n`
  - `strictMono_consec_is_id` — a consecutively strictly-increasing function on `Fin n` is the identity
-/

def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ ⦃a b⦄, f a = f b → a = b

variable {α : Type} [DecidableEq α]

-- indexOf_cons spells out the cons case; used throughout.
-- Note the argument order: x == y (head == needle).
theorem indexOf_cons_eq (x y : α) (xs : List α) (h : x = y) :
    (x :: xs).indexOf y = 0 := by
  subst h; simp [List.indexOf_cons]

theorem indexOf_cons_ne (x y : α) (xs : List α) (h : x ≠ y) :
    (x :: xs).indexOf y = xs.indexOf y + 1 := by
  simp only [List.indexOf_cons]
  cases hb : (x == y) with
  | true  => exact absurd (by simpa using hb) h
  | false => rfl


/-- The indexOf of the element at position k is k, for Nodup lists. -/
theorem indexOf_getElem {l : List α} (hnd : l.Nodup)
    (k : Nat) (hk : k < l.length) :
    l.indexOf (l[k]'hk) = k := by
  induction l generalizing k with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons x xs ih =>
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero]
      simp [indexOf_cons_eq x x xs rfl]
    | succ k =>
      have hk' : k < xs.length := Nat.lt_of_succ_lt_succ hk
      have hnd' : xs.Nodup := hnd.of_cons
      have hxnmem : x ∉ xs := List.nodup_cons.mp hnd |>.1
      have hne : x ≠ xs[k]'hk' := fun h => hxnmem (h ▸ List.getElem_mem hk')
      simp only [List.getElem_cons_succ]
      rw [indexOf_cons_ne x (xs[k]'hk') xs hne]
      exact congrArg (· + 1) (ih hnd' k hk')

/-!
  ## Finite surjectivity (pigeonhole for Fin n)

  `Fin.mem_of_nodup_length` is the core surjectivity result: a Nodup list
  of `Fin n` with length `n` must contain every element.  The proof proceeds
  by induction on `n`, using a compression map that removes one element from
  `Fin (n+1)` to produce an element of `Fin n`.

-/

/-- Compress Fin (n+1) to Option (Fin n) by omitting the value a.
    Returns none iff x = a; injective on Some values. -/
private def compressOpt {n : Nat} (a : Fin (n+1)) (x : Fin (n+1)) : Option (Fin n) :=
  if hlt : x.val < a.val then
    some ⟨x.val, by omega⟩
  else if _heq : x.val = a.val then
    none
  else
    some ⟨x.val - 1, by omega⟩

private theorem compressOpt_ne_none {n : Nat} (a : Fin (n+1)) (x : Fin (n+1))
    (h : x ≠ a) : ∃ v, compressOpt a x = some v := by
  unfold compressOpt
  by_cases hlt : x.val < a.val
  · rw [dif_pos hlt]; exact ⟨_, rfl⟩
  · rw [dif_neg hlt]
    by_cases heq : x.val = a.val
    · rw [dif_pos heq]; exact absurd (Fin.ext heq) h
    · rw [dif_neg heq]; exact ⟨_, rfl⟩

private theorem compressOpt_injective {n : Nat} (a : Fin (n+1))
    (x y : Fin (n+1)) (v : Fin n)
    (hx : compressOpt a x = some v) (hy : compressOpt a y = some v) : x = y := by
  unfold compressOpt at hx hy
  by_cases hltx : x.val < a.val
  · rw [dif_pos hltx] at hx
    -- hx : some ⟨x.val, _⟩ = some v, so x.val = v.val
    have hvx : x.val = v.val := congrArg Fin.val (Option.some.inj hx)
    by_cases hlty : y.val < a.val
    · rw [dif_pos hlty] at hy
      have hvy : y.val = v.val := congrArg Fin.val (Option.some.inj hy)
      exact Fin.ext (by omega)
    · rw [dif_neg hlty] at hy
      by_cases heqy : y.val = a.val
      · rw [dif_pos heqy] at hy; exact absurd hy (Option.noConfusion)
      · rw [dif_neg heqy] at hy
        -- hx : x.val < a.val, hy : y.val - 1 = v.val = x.val; contradiction
        have hvy : y.val - 1 = v.val := congrArg Fin.val (Option.some.inj hy)
        exfalso; omega
  · rw [dif_neg hltx] at hx
    by_cases heqx : x.val = a.val
    · rw [dif_pos heqx] at hx; exact absurd hx (Option.noConfusion)
    · rw [dif_neg heqx] at hx
      have hvx : x.val - 1 = v.val := congrArg Fin.val (Option.some.inj hx)
      by_cases hlty : y.val < a.val
      · rw [dif_pos hlty] at hy
        have hvy : y.val = v.val := congrArg Fin.val (Option.some.inj hy)
        exfalso; omega
      · rw [dif_neg hlty] at hy
        by_cases heqy : y.val = a.val
        · rw [dif_pos heqy] at hy; exact absurd hy (Option.noConfusion)
        · rw [dif_neg heqy] at hy
          have hvy : y.val - 1 = v.val := congrArg Fin.val (Option.some.inj hy)
          exact Fin.ext (by omega)

/-- If every element of l maps to `some`, filterMap preserves length. -/
private theorem filterMap_length_of_all_some {α β : Type} {f : α → Option β} {l : List α}
    (h : ∀ a ∈ l, ∃ b, f a = some b) : (l.filterMap f).length = l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨b, hb⟩ := h hd (List.mem_cons_self hd tl)
    have hcons : (hd :: tl).filterMap f = b :: tl.filterMap f := by
      simp [hb]
    rw [hcons, List.length_cons, List.length_cons]
    congr 1
    exact ih (fun a ha => h a (List.mem_cons_of_mem hd ha))

/-- A Nodup list of Fin n with length n contains every element of Fin n. -/
theorem Fin.mem_of_nodup_length {n : Nat} {l : List (Fin n)}
    (hnd : l.Nodup) (hlen : l.length = n) (c : Fin n) : c ∈ l := by
  induction n with
  | zero => exact c.elim0
  | succ n ih =>
    match l, hlen with
    | [], h => exact absurd h (by simp)
    | hd :: tl, h =>
      have hlen_tl : tl.length = n := by
        have := h; rw [List.length_cons] at this; omega
      have hnd_tl : tl.Nodup := hnd.of_cons
      have hhd_notin : hd ∉ tl := (List.nodup_cons.mp hnd).1
      by_cases heq : c = hd
      · exact heq ▸ List.mem_cons_self hd tl
      · -- Compress tl : List (Fin (n+1)) into a List (Fin n) by removing hd.
        -- All elements of tl are ≠ hd (since hd ∉ tl), so compressOpt hd always
        -- returns some. The compressed list is Nodup with length n; by IH it
        -- contains every Fin n element, including compressOpt hd c.
        have hmem_tl : ∀ x ∈ tl, x ≠ hd := fun x hx heqx => hhd_notin (heqx ▸ hx)
        have hall : ∀ x ∈ tl, ∃ b, compressOpt hd x = some b :=
          fun x hx => compressOpt_ne_none hd x (hmem_tl x hx)
        have hlen' : (tl.filterMap (compressOpt hd)).length = n :=
          (filterMap_length_of_all_some hall).trans hlen_tl
        have hnd' : (tl.filterMap (compressOpt hd)).Nodup :=
          List.Nodup.filterMap hnd_tl
            (fun a _ b _ v ha hb => compressOpt_injective hd a b v ha hb)
        -- compressOpt hd c returns some v (since c ≠ hd)
        obtain ⟨v, hcv⟩ := compressOpt_ne_none hd c heq
        -- By IH, v is in the compressed list
        have hv_in : v ∈ tl.filterMap (compressOpt hd) := ih hnd' hlen' v
        -- Unpack: some x in tl maps to v under compressOpt hd
        rw [List.mem_filterMap] at hv_in
        obtain ⟨x, hx_mem, hx_v⟩ := hv_in
        -- Injectivity: x = c
        have hxc : x = c := compressOpt_injective hd x c v hx_v hcv
        exact List.mem_cons.mpr (Or.inr (hxc ▸ hx_mem))

/-! ## Computable inverse of an injective Fin n → Fin n -/

private def preimgList {n : Nat} (f : Fin n → Fin n) : List (Fin n) :=
  (List.finRange n).map f

private theorem preimgList_nodup {n : Nat} {f : Fin n → Fin n} (hinj : Injective f) :
    (preimgList f).Nodup :=
  (nodup_finRange n).map (f := f) (fun _a _b hne heq => hne (hinj heq))

private theorem preimgList_length {n : Nat} (f : Fin n → Fin n) :
    (preimgList f).length = n := by simp [preimgList]

private theorem mem_preimgList {n : Nat} {f : Fin n → Fin n} (hinj : Injective f) (k : Fin n) :
    k ∈ preimgList f :=
  Fin.mem_of_nodup_length (preimgList_nodup hinj) (preimgList_length f) k

/-- The computable inverse of an injective Fin n → Fin n. -/
def Fin.invOf {n : Nat} {f : Fin n → Fin n} (hinj : Injective f) (k : Fin n) : Fin n :=
  ⟨(preimgList f).indexOf k, by
    have h1 := indexOf_lt_length (mem_preimgList hinj k)
    have h2 := preimgList_length f
    omega⟩

theorem Fin.invOf_right {n : Nat} {f : Fin n → Fin n} (hinj : Injective f) (k : Fin n) :
    f (Fin.invOf hinj k) = k := by
  have hlt  := indexOf_lt_length (mem_preimgList hinj k)
  have hget : (preimgList f)[(preimgList f).indexOf k]'hlt = k :=
    getElem_indexOf (mem_preimgList hinj k)
  simp only [preimgList, List.getElem_map] at hget
  simpa using hget

theorem Fin.invOf_left {n : Nat} {f : Fin n → Fin n} (hinj : Injective f) (c : Fin n) :
    Fin.invOf hinj (f c) = c := Fin.ext (by
  have hclt : c.val < (preimgList f).length := by rw [preimgList_length]; exact c.isLt
  have himg_c : (preimgList f)[c.val]'hclt = f c := by
    simp [preimgList, List.getElem_map]
  rw [← himg_c]
  exact indexOf_getElem (preimgList_nodup hinj) c.val hclt)

/-- A function Fin n → Fin n that is strictly increasing at every consecutive pair
    must be the identity. -/
theorem strictMono_consec_is_id {n : Nat} (f : Fin n → Fin n)
    (hmono : ∀ k (hk : k + 1 < n), f ⟨k, by omega⟩ < f ⟨k + 1, hk⟩)
    (k : Fin n) : f k = k := by
  have f_ge : ∀ j (hj : j < n), j ≤ (f ⟨j, hj⟩).val := by
    intro j
    induction j with
    | zero => intro; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hstep := hmono j hj
      have hprev := ih (by omega)
      omega
  have f_le : ∀ j (hj : j < n), (f ⟨j, hj⟩).val ≤ j := by
    intro j hj
    have chain : ∀ m (hm : j + m < n),
        (f ⟨j, hj⟩).val + m ≤ (f ⟨j + m, by omega⟩).val := by
      intro m
      induction m with
      | zero => intro; simp
      | succ m ih =>
        intro hm
        have step : (f ⟨j + m, by omega⟩).val < (f ⟨j + (m + 1), hm⟩).val :=
          hmono (j + m) hm
        have prev := ih (by omega)
        omega
    have final := chain (n - 1 - j) (by omega)
    -- Extract the nat equality first so omega has hj in scope
    have hjn  : j + (n - 1 - j) = n - 1 := by omega
    have hn1  : n - 1 < n             := by omega
    have hval : (f ⟨j + (n - 1 - j), by omega⟩).val = (f ⟨n - 1, hn1⟩).val :=
      congrArg (fun x => (f x).val) (Fin.ext hjn)
    have hfinal : (f ⟨j, hj⟩).val + (n - 1 - j) ≤ (f ⟨n - 1, hn1⟩).val :=
      Nat.le_trans final (Nat.le_of_eq hval)
    have bound := (f ⟨n - 1, hn1⟩).isLt
    omega
  exact Fin.ext (Nat.le_antisymm (f_le k.val k.isLt) (f_ge k.val k.isLt))
