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
sorry
