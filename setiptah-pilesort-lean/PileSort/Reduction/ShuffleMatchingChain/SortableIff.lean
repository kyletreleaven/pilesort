import PileSort.Reduction.ShuffleMatchingChain.ChangeProfiles
import PileSort.MatchingChain.Mono
import PileSort.Shuffle.Properties

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
  have := d.left_inv s
  rw [h, d.left_inv t] at this
  exact this.symm

/-- For consecutive card values s and s+1, output is sorted at that pair iff
    compile types act (assign s) ≤ assign s+1,
    where act is the ascent/descent of s in d. -/
theorem compile_consecutive {n : Nat} (d : Deck n) (types : List PileType)
    (assign : Fin n → Fin types.length) (s : Fin n) (hs : s.val + 1 < n) :
    let s' : Fin n := ⟨s.val + 1, hs⟩
    let act : Action := if d.posOf s < d.posOf s' then .a else .d
    (shuffleRound d types assign).posOf s < (shuffleRound d types assign).posOf s' ↔
    compile types act (assign s).val ≤ (assign s').val := by
  let s' : Fin n := ⟨s.val + 1, hs⟩
  have hposne : d.posOf s ≠ d.posOf s' :=
    fun h => Fin.ne_of_lt (Fin.mk_lt_mk.mpr (by omega)) (d.posOf_injective h)
  apply (shuffleRound_consecutive d types assign s hs).trans
  rw [compile_eq, stays_iff (assign s) (assign s')
        ((types.get (assign s) = .Q ∧ d.posOf s < d.posOf s') ∨
         (types.get (assign s) = .S ∧ d.posOf s' < d.posOf s))]
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
