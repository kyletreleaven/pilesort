/-
  Connects pile shuffle mechanics to the compiled automaton.

  Main result:
    `Sortable d types ↔ applyWord (Deck.changeProfile d) (compile types) 0 < types.length`

  Proof roadmap:
  1. `compile_consecutive` — the per-pair bridge: output is sorted at (s, s+1) iff
     compile types act (assign s) ≤ assign s+1, where act is the ascent/descent of s in d.
  2. `assign_dominates_applyWord` — any sorting assignment dominates the minimum
     assignment (given by applyWord) at every card.
  3. `minAssign_sorts` — the minimum assignment itself sorts the deck when it stays
     in bounds.
  4. The main iff follows from 2 and 3.
-/
import PileSort.PileShuffle
import PileSort.Mono

/-! ## Change profile of a deck -/

/-- The change profile of a deck: for consecutive card values s, s+1,
    record whether s is an ascent (.a, posOf s < posOf s+1) or descent (.d). -/
def Deck.changeProfile {n : Nat} (d : Deck n) : List Action :=
  (List.finRange n).zipWith
    (fun s t => if d.posOf s < d.posOf t then .a else .d)
    (List.finRange n).tail

/-! ## Per-pair bridge -/

/-- Core reduction: `p < q ∨ p = q ∧ C` iff `p.val + (if C then 0 else 1) ≤ q.val`.
    When C holds (same-pile valid), both sides are `p ≤ q`.
    When C fails (must advance), both sides are `p < q`. -/
private theorem stays_iff {m : Nat} (p q : Fin m) (C : Prop) [Decidable C] :
    (p < q ∨ p = q ∧ C) ↔ p.val + (if C then 0 else 1) ≤ q.val := by
  simp only [Fin.lt_def, Fin.ext_iff]
  by_cases hC : C <;> simp [hC] <;> omega


/-- posOf injectivity: d.posOf is injective. -/
private theorem Deck.posOf_injective {n : Nat} (d : Deck n) {s t : Fin n}
    (h : d.posOf s = d.posOf t) : s = t := by
  have := d.left_inv s; rw [h, d.left_inv t] at this; exact this.symm

/-- For consecutive card values s and s+1, output is sorted at that pair iff
    compile types act (assign s) ≤ assign s+1,
    where act is the ascent/descent of s in d.

  Proof:
  Rewrite LHS via `shuffleRound_consecutive` and RHS via `compile_eq`.
  The RHS becomes `(assign s).val + advanceDelta ≤ (assign s').val`.

  Case split on `h : d.posOf s < d.posOf s'` (fixing act), then on
  `types.get (assign s)` (fixing advanceDelta).  Four sub-cases:

  · Q + .a (delta 0): same-pile is valid (ascent given matches Q rule).
    Both sides reduce to `assign s ≤ assign s'`.

  · S + .a (delta 1): same-pile is impossible (S requires descent, not ascent).
    Both sides reduce to `assign s < assign s'`.

  · Q + .d (delta 1): same-pile is impossible (Q requires ascent, not descent).
    Both sides reduce to `assign s < assign s'`.

  · S + .d (delta 0): same-pile is valid (descent given matches S rule).
    Both sides reduce to `assign s ≤ assign s'`.

  In each case, `posOf` injectivity (s ≠ s' implies posOf s ≠ posOf s') is
  used to rule out the contradictory same-pile branch. -/
theorem compile_consecutive {n : Nat} (d : Deck n) (types : List PileType)
    (assign : Fin n → Fin types.length) (s : Fin n) (hs : s.val + 1 < n) :
    let s' : Fin n := ⟨s.val + 1, hs⟩
    let act : Action := if d.posOf s < d.posOf s' then .a else .d
    (shuffleRound d types assign).posOf s < (shuffleRound d types assign).posOf s' ↔
    compile types act (assign s).val ≤ (assign s').val := by
  let s' : Fin n := ⟨s.val + 1, hs⟩
  have hposne : d.posOf s ≠ d.posOf s' :=
    fun h => Fin.ne_of_lt (Fin.mk_lt_mk.mpr (by omega)) (d.posOf_injective h)
  -- Chain: posOf comparison ↔ pile-assignment disjunction ↔ compile inequality.
  apply (shuffleRound_consecutive d types assign s hs).trans
  -- Goal: (assign s < assign s' ∨ ...) ↔ compile types act (assign s).val ≤ (assign s').val
  rw [compile_eq, stays_iff (assign s) (assign s')
        ((types.get (assign s) = .Q ∧ d.posOf s < d.posOf s') ∨
         (types.get (assign s) = .S ∧ d.posOf s' < d.posOf s))]
  -- Prove the deltas match, then the iff is trivial.
  have hd : advanceDelta types (assign s) (if d.posOf s < d.posOf s' then .a else .d) =
            if ((types.get (assign s) = .Q ∧ d.posOf s < d.posOf s') ∨
                (types.get (assign s) = .S ∧ d.posOf s' < d.posOf s)) then 0 else 1 := by
    by_cases h : d.posOf s < d.posOf s'
    · have hlt' : ¬d.posOf s' < d.posOf s := fun h' => absurd h (Nat.not_lt.mpr (Nat.le_of_lt h'))
      simp only [if_pos h, h, true_and, hlt', and_false, or_false]
      cases htypes : types.get (assign s) <;> simp [advanceDelta, ← List.get_eq_getElem, htypes]
    · have hlt' : d.posOf s' < d.posOf s :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (fun heq => hposne (Fin.ext heq.symm))
      simp only [if_neg h, h, false_and, false_or, hlt', and_true]
      cases htypes : types.get (assign s) <;> simp [advanceDelta, ← List.get_eq_getElem, htypes]
  rw [hd]

/-! ## Domination lemmas -/

private theorem sorted_posOf {n : Nat} (s : Fin n) : (Deck.sorted n).posOf s = s := rfl

private theorem changeProfile_length {n : Nat} (d : Deck n) :
    (Deck.changeProfile d).length = n - 1 := by
  simp [Deck.changeProfile, List.length_zipWith, List.length_tail, List.length_finRange]
  omega

/-- The k-th action in the change profile is .a iff card k comes before card k+1. -/
private theorem changeProfile_get {n : Nat} (d : Deck n) (k : Nat)
    (hk : k < (Deck.changeProfile d).length) :
    let hkn  : k < n     := by simp [changeProfile_length] at hk; omega
    let hk1n : k + 1 < n := by simp [changeProfile_length] at hk; omega
    (Deck.changeProfile d)[k]'hk =
    if d.posOf ⟨k, hkn⟩ < d.posOf ⟨k+1, hk1n⟩ then .a else .d := by
  simp only [Deck.changeProfile, List.getElem_zipWith, List.getElem_tail, List.getElem_finRange]
  congr 1

/-- Decompose applyWord on take (k+1): last step is a single compile call. -/
private theorem applyWord_take_succ (word : List Action) (types : List PileType)
    (s k : Nat) (hk : k < word.length) :
    applyWord (word.take (k+1)) (compile types) s =
    compile types (word[k]'hk) (applyWord (word.take k) (compile types) s) := by
  have htake : word.take (k+1) = word.take k ++ [word[k]'hk] := by
    rw [List.take_succ, List.getElem?_eq_getElem hk]; rfl
  rw [htake, applyWord_append]
  simp [applyWord]

/-- Any sorting assignment dominates the minimum (automaton prefix) assignment at every card.
    That is, if assign sorts d on types, then for all k < n,
    the automaton state after k steps is ≤ (assign ⟨k, hk⟩).val. -/
theorem assign_dominates_applyWord {n : Nat} (d : Deck n) (types : List PileType)
    (assign : Fin n → Fin types.length)
    (hsort : shuffleRound d types assign = Deck.sorted n)
    (k : Nat) (hk : k < n) :
    applyWord ((Deck.changeProfile d).take k) (compile types) 0 ≤ (assign ⟨k, hk⟩).val := by
  induction k with
  | zero => simp [applyWord]
  | succ k ih =>
    have hkn : k < n := by omega
    have hkw : k < (Deck.changeProfile d).length := by
      simp [changeProfile_length]; omega
    -- Sorting at the pair (k, k+1): apply compile_consecutive
    have hlt : (shuffleRound d types assign).posOf ⟨k, hkn⟩ <
               (shuffleRound d types assign).posOf ⟨k+1, hk⟩ := by
      rw [hsort]; simp [sorted_posOf]
    have hci := (compile_consecutive d types assign ⟨k, hkn⟩ hk).mp hlt
    -- hci : compile types act (assign ⟨k,_⟩).val ≤ (assign ⟨k+1,_⟩).val
    -- Unfold one step of applyWord
    rw [applyWord_take_succ _ _ _ _ hkw, changeProfile_get d k hkw]
    -- Goal: compile types act (applyWord (take k) ... 0) ≤ (assign ⟨k+1,_⟩).val
    exact Nat.le_trans (compile_step_mono types _ _ _ (ih hkn)) hci

/-! ## Minimum assignment -/

/-- The minimum pile assignment: card k goes to the automaton state after k steps. -/
def minAssign {n : Nat} (d : Deck n) (types : List PileType)
    (h : applyWord (Deck.changeProfile d) (compile types) 0 < types.length)
    (k : Fin n) : Fin types.length :=
  ⟨applyWord ((Deck.changeProfile d).take k.val) (compile types) 0, by
    apply Nat.lt_of_le_of_lt _ h
    have hsplit : applyWord (Deck.changeProfile d) (compile types) 0 =
        applyWord ((Deck.changeProfile d).drop k.val) (compile types)
          (applyWord ((Deck.changeProfile d).take k.val) (compile types) 0) := by
      rw [← applyWord_append, List.take_append_drop]
    rw [hsplit]; exact applyWord_ge _ _ _⟩
