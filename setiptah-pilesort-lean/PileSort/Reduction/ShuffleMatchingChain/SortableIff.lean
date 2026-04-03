import PileSort.Reduction.ShuffleMatchingChain.ChangeProfiles
import PileSort.MatchingChain.Mono
import PileSort.Shuffle.Properties

/-!
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

/-- Decompose applyWord on take (k+1): last step is a single compile call. -/
private theorem applyWord_take_succ (word : List Action) (types : List PileType)
    (s k : Nat) (hk : k < word.length) :
    applyWord (word.take (k+1)) (compile types) s =
    compile types (word[k]'hk) (applyWord (word.take k) (compile types) s) := by
  have htake : word.take (k+1) = word.take k ++ [word[k]'hk] := by
    rw [List.take_succ, List.getElem?_eq_getElem hk]
    rfl
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
      simp [changeProfile_length]
      omega
    have hlt : (shuffleRound d types assign).posOf ⟨k, hkn⟩ <
               (shuffleRound d types assign).posOf ⟨k+1, hk⟩ := by
      rw [hsort]
      simp [Deck.sorted]
    have hci := (compile_consecutive d types assign ⟨k, hkn⟩ hk).mp hlt
    rw [applyWord_take_succ _ _ _ _ hkw, changeProfile_get d k hkw]
    exact Nat.le_trans (compile_step_mono types _ _ _ (ih hkn)) hci

/-! ## Minimum assignment and its properties -/

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
    rw [hsplit]
    exact applyWord_ge _ _ _⟩

/-- The successor step of minAssign equals one compile call on the predecessor. -/
theorem minAssign_consecutive {n : Nat} (d : Deck n) (types : List PileType)
    (h : applyWord (Deck.changeProfile d) (compile types) 0 < types.length)
    (k : Nat) (hk : k + 1 < n) :
    let hkw : k < (Deck.changeProfile d).length := by simp [changeProfile_length]; omega
    (minAssign d types h ⟨k + 1, hk⟩).val =
    compile types ((Deck.changeProfile d)[k]'hkw) (minAssign d types h ⟨k, by omega⟩).val :=
  applyWord_take_succ _ _ _ _ (by simp [changeProfile_length]; omega)

/-- The minimum assignment sorts the deck. -/
theorem minAssign_sorts {n : Nat} (d : Deck n) (types : List PileType)
    (h : applyWord (Deck.changeProfile d) (compile types) 0 < types.length) :
    shuffleRound d types (minAssign d types h) = Deck.sorted n := by
  have hposOf : (shuffleRound d types (minAssign d types h)).posOf = id := by
    funext k
    apply strictMono_consec_is_id
    intro j hj
    apply (compile_consecutive d types (minAssign d types h) ⟨j, by omega⟩ hj).mpr
    have hkw : j < (Deck.changeProfile d).length := by simp [changeProfile_length]; omega
    rw [minAssign_consecutive d types h j hj, changeProfile_get d j hkw]
    exact Nat.le_refl _
  have hcardAt : (shuffleRound d types (minAssign d types h)).cardAt = id := by
    funext k
    have hpk : (shuffleRound d types (minAssign d types h)).posOf k = k :=
      congrFun hposOf k
    have hlv := (shuffleRound d types (minAssign d types h)).left_inv k
    rw [hpk] at hlv
    exact hlv
  apply Deck.ext
  · rw [hposOf]
    rfl
  · rw [hcardAt]
    rfl

/-! ## Main theorem -/

/-- A deck is sortable by a pile type list iff the automaton (compile types) accepts
    the deck's change profile starting from state 0 (i.e., ends in a valid state). -/
theorem sortable_iff_accepts {n : Nat} (hn : 0 < n) (d : Deck n) (types : List PileType) :
    Sortable d types ↔ accepts types (Deck.changeProfile d) := by
  constructor
  · intro ⟨assign, hsort⟩
    have hk : n - 1 < n := by omega
    have hdom := assign_dominates_applyWord d types assign hsort (n - 1) hk
    have htake : (Deck.changeProfile d).take (n - 1) = Deck.changeProfile d := by
      apply List.take_of_length_le
      simp [changeProfile_length]
    rw [htake] at hdom
    exact Nat.lt_of_le_of_lt hdom (assign ⟨n - 1, hk⟩).isLt
  · intro h
    exact ⟨minAssign d types h, minAssign_sorts d types h⟩
