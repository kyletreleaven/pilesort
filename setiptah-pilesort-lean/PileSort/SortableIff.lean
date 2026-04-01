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
import PileSort.Reduction
import PileSort.Reduction.ShuffleMatchingChain.SortableIff

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
      rw [hsort]
      simp [Deck.sorted]
    have hci := (compile_consecutive d types assign ⟨k, hkn⟩ hk).mp hlt
    -- hci : compile types act (assign ⟨k,_⟩).val ≤ (assign ⟨k+1,_⟩).val
    -- Unfold one step of applyWord
    rw [applyWord_take_succ _ _ _ _ hkw, changeProfile_get d k hkw]
    -- Goal: compile types act (applyWord (take k) ... 0) ≤ (assign ⟨k+1,_⟩).val
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
    rw [hsplit]; exact applyWord_ge _ _ _⟩

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
  -- Step 1: posOf = id via strictMono_consec_is_id
  have hposOf : (shuffleRound d types (minAssign d types h)).posOf = id := by
    funext k
    apply strictMono_consec_is_id
    intro j hj
    apply (compile_consecutive d types (minAssign d types h) ⟨j, by omega⟩ hj).mpr
    have hkw : j < (Deck.changeProfile d).length := by simp [changeProfile_length]; omega
    rw [minAssign_consecutive d types h j hj, changeProfile_get d j hkw]
    exact Nat.le_refl _
  -- Step 2: cardAt = id via left_inv + posOf = id
  have hcardAt : (shuffleRound d types (minAssign d types h)).cardAt = id := by
    funext k
    have hpk : (shuffleRound d types (minAssign d types h)).posOf k = k :=
      congrFun hposOf k
    have hlv := (shuffleRound d types (minAssign d types h)).left_inv k
    rw [hpk] at hlv
    exact hlv
  -- Step 3: Deck.ext
  apply Deck.ext
  · rw [hposOf]; rfl
  · rw [hcardAt]; rfl

/-! ## Main theorem -/

/-- A deck is sortable by a pile type list iff the automaton (compile types) accepts
    the deck's change profile starting from state 0 (i.e., ends in a valid state). -/
theorem sortable_iff_accepts {n : Nat} (hn : 0 < n) (d : Deck n) (types : List PileType) :
    Sortable d types ↔ accepts types (Deck.changeProfile d) := by
  constructor
  · -- Forward: extract assign from Sortable, apply assign_dominates_applyWord at k = n-1.
    intro ⟨assign, hsort⟩
    have hk : n - 1 < n := by omega
    have hdom := assign_dominates_applyWord d types assign hsort (n - 1) hk
    -- (changeProfile d).take (n-1) = changeProfile d, since length = n-1
    have htake : (Deck.changeProfile d).take (n - 1) = Deck.changeProfile d := by
      apply List.take_of_length_le
      simp [changeProfile_length]
    rw [htake] at hdom
    exact Nat.lt_of_le_of_lt hdom (assign ⟨n - 1, hk⟩).isLt
  · -- Backward: witness minAssign, use minAssign_sorts.
    intro h
    exact ⟨minAssign d types h, minAssign_sorts d types h⟩
