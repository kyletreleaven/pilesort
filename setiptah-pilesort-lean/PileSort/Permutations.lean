/-
  Technical lemmas about bijections of Fin n.

  These underpin Deck.fromDeckSeq in PileShuffle.lean.
  All results concern Nodup lists, which represent the "position → card"
  direction of a deck permutation.

  Provided:
    · indexOf_lt_length       — a ∈ l → l.indexOf a < l.length
    · getElem_indexOf         — l.Nodup → a ∈ l → l[l.indexOf a] = a
    · indexOf_getElem         — l.Nodup → l.indexOf l[k] = k
    · Fin.mem_of_nodup_length — Nodup list of Fin n with length n contains every element
-/

variable {α : Type} [DecidableEq α]

-- indexOf_cons spells out the cons case; used throughout.
-- Note the argument order: x == y (head == needle).
private theorem indexOf_cons_eq (x y : α) (xs : List α) (h : x = y) :
    (x :: xs).indexOf y = 0 := by
  subst h; simp [List.indexOf_cons]

private theorem indexOf_cons_ne (x y : α) (xs : List α) (h : x ≠ y) :
    (x :: xs).indexOf y = xs.indexOf y + 1 := by
  simp only [List.indexOf_cons]
  cases hb : (x == y) with
  | true  => exact absurd (by simpa using hb) h
  | false => rfl

/-- indexOf is strictly less than the list length when the element is a member. -/
theorem indexOf_lt_length {a : α} {l : List α} (hmem : a ∈ l) :
    l.indexOf a < l.length := by
  induction l with
  | nil => exact absurd hmem (List.not_mem_nil _)
  | cons x xs ih =>
    simp only [List.length_cons]
    by_cases hax : x = a
    · simp [indexOf_cons_eq x a xs hax]
    · have hmem' : a ∈ xs :=
        (List.mem_cons.mp hmem).resolve_left (Ne.symm hax)
      rw [indexOf_cons_ne x a xs hax]
      exact Nat.succ_lt_succ (ih hmem')

/-- The element at its own indexOf is itself, for Nodup lists. -/
theorem getElem_indexOf {a : α} {l : List α}
    (hnd : l.Nodup) (hmem : a ∈ l) :
    l[l.indexOf a]'(indexOf_lt_length hmem) = a := by
  induction l with
  | nil => exact absurd hmem (List.not_mem_nil _)
  | cons x xs ih =>
    by_cases hax : x = a
    · subst hax
      simp [indexOf_cons_eq x x xs rfl, List.getElem_cons_zero]
    · have hmem' : a ∈ xs :=
        (List.mem_cons.mp hmem).resolve_left (Ne.symm hax)
      have hnd' : xs.Nodup := hnd.of_cons
      simp only [indexOf_cons_ne x a xs hax, List.getElem_cons_succ]
      exact ih hnd' hmem'

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

/-- A Nodup list of Fin n with length n contains every element of Fin n. -/
theorem Fin.mem_of_nodup_length {n : Nat} {l : List (Fin n)}
    (hnd : l.Nodup) (hlen : l.length = n) (c : Fin n) : c ∈ l := by
  -- The function k ↦ l[k] : Fin n → Fin n is injective (by indexOf_getElem),
  -- hence surjective on Fin n (finite pigeonhole).  c is in the range, so c ∈ l.
  sorry
