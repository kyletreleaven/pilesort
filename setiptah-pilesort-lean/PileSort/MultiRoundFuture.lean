import PileSort.MultiRoundCommon

/-!
  Experimental redesign space for `PileSort.MultiRound`.

  This file is intended to host a parallel development of the multi-round
  folding/unfolding pipeline without destabilizing `PileSort/MultiRound.lean`.

  ## Motivation

  The hard local proofs in `MultiRound.lean` do not appear false; the main issue
  is that the current fold/orientation is awkward for the inverse theorems we
  want.

  The current implementation tends to treat the accumulator as "what has already
  been folded".  The alternative semantic picture under investigation here is:

  · the current round is the left/current input;
  · the accumulator represents the effect of all future rounds;
  · recursion should therefore align with `current :: future`.

  In that interpretation, the current transport/cast obligations around local
  inversion lemmas are likely symptoms of an orientation mismatch rather than of
  real mathematical difficulty.

  ## TODOs

  Current status:

  1. `foldVirtualPileTypesFuture` defined.
  2. Future-oriented `foldedAssign` defined.
  3. Future-oriented `unfoldedAssign` defined.

  Next steps in this file:

  1. Check whether the common binary layer (`combinedAssign`, `splitAssign`,
     `combinedAssign_split`) is sufficient unchanged.
  2. Prove the basic recursion equations and type-list equations for the three
     new definitions.
  3. Rebuild the forward composition theorem
     `multiShuffleRound_eq_shuffleRound`.
     This is the critical direction: it should drive the forward implication in
     `multiSortable_iff_sortable`.
  4. Rebuild the local equivalence theorem
     `multiSortable_iff_sortable` against the new orientation.
  5. Rebuild the remaining inverse/decomposition support theorems used for the
     backward implication.

  The goal is to keep names natural in this file and switch over later at the
  module/import boundary once the redesign is stable.  In particular, a major
  success criterion for this file is a clean reproving of
  `multiSortable_iff_sortable`, with the proof split as:

  · forward: composition correctness via `multiShuffleRound_eq_shuffleRound`;
  · backward: existence of an inverse decomposition via `unfoldedAssign`.
-/

/-- Fold round types in current/future orientation:
    the head of the list is the current round, and the recursive result
    represents the effect of all future rounds. -/
def foldVirtualPileTypesFuture : List (List PileType) → List PileType
  | [] => [PileType.Q]
  | current :: future => virtualPileTypes current (foldVirtualPileTypesFuture future)

/-- Fold per-round assignments in the same current/future orientation. -/
def foldedAssign {n : Nat} :
    (specs : List (ShuffleSpec n)) →
    Fin n → Fin (foldVirtualPileTypesFuture (specs.map (·.types))).length
  | [], c => ⟨0, by simp [foldVirtualPileTypesFuture]⟩
  | current :: future, c =>
      show Fin
        (virtualPileTypes current.types
          (foldVirtualPileTypesFuture (future.map (·.types)))).length from
      combinedAssign current.types
        (foldVirtualPileTypesFuture (future.map (·.types)))
        current.assign
        (foldedAssign future)
        c

/-- Unfold a combined assignment by splitting off the current round and
    recurring on the future suffix. -/
def unfoldedAssign {n : Nat} :
    (rounds : List (List PileType)) →
    (Fin n → Fin (foldVirtualPileTypesFuture rounds).length) →
    List (ShuffleSpec n)
  | [], _ => []
  | current :: future, assign =>
      let split := fun c =>
        splitAssign current (foldVirtualPileTypesFuture future) (assign c)
      ⟨current, fun c => (split c).1⟩ :: unfoldedAssign future (fun c => (split c).2)

/-- One-step equation for the future-oriented pile-type fold.
    This is just the defining equation (`rfl`), recorded only as a named rewrite
    rule in case later proofs read more clearly using it explicitly. -/
theorem foldVirtualPileTypesFuture_cons (current : List PileType)
    (future : List (List PileType)) :
    foldVirtualPileTypesFuture (current :: future) =
    virtualPileTypes current (foldVirtualPileTypesFuture future) := by
  rfl

/-- One-step equation for the future-oriented assignment fold.
    This should expose that the current-round assignment is combined with the
    recursively folded future assignment via `combinedAssign`. -/
theorem foldedAssign_cons {n : Nat} (current : ShuffleSpec n)
    (future : List (ShuffleSpec n)) :
    foldedAssign (current :: future) =
    fun c =>
      combinedAssign current.types
        (foldVirtualPileTypesFuture (future.map (·.types)))
        current.assign
        (foldedAssign future)
        c := by
  funext c
  rfl

/-- One-step equation for the future-oriented unfolding procedure.
    This should expose that we split the combined assignment into a current
    assignment and a recursive future assignment.  It is the basic rewrite rule
    for the inverse direction. -/
theorem unfoldedAssign_cons {n : Nat} (current : List PileType)
    (future : List (List PileType))
    (assign : Fin n → Fin (foldVirtualPileTypesFuture (current :: future)).length) :
    unfoldedAssign (current :: future) assign =
    let split := fun c =>
      splitAssign current (foldVirtualPileTypesFuture future) (assign c)
    ⟨current, fun c => (split c).1⟩ :: unfoldedAssign future (fun c => (split c).2) := by
  rfl

/-- Critical forward composition theorem for the future-oriented fold:
    executing many rounds left-to-right equals one round on the folded future
    virtual pile types with the folded assignment. -/
theorem multiShuffleRound_eq_shuffleRound {n : Nat} (d : Deck n)
    (specs : List (ShuffleSpec n)) :
    multiShuffleRound d specs =
    shuffleRound d
      (foldVirtualPileTypesFuture (specs.map (·.types)))
      (foldedAssign specs) := by
  sorry

/-- The reconstructed specs from `unfoldedAssign` have exactly the requested
    round-type list.  This is needed to build the witness in the backward
    implication of `multiSortable_iff_sortable`. -/
theorem unfoldedAssign_types {n : Nat} (rounds : List (List PileType))
    (assign : Fin n → Fin (foldVirtualPileTypesFuture rounds).length) :
    (unfoldedAssign rounds assign).map (·.types) = rounds := by
  sorry

/-- Pointwise roundtrip: folding the specs reconstructed by `unfoldedAssign`
    recovers the original folded assignment value on each card.  This is the
    main inverse statement needed for the backward implication. -/
theorem foldedAssign_unfoldedAssign_val {n : Nat} (rounds : List (List PileType))
    (assign : Fin n → Fin (foldVirtualPileTypesFuture rounds).length) (c : Fin n) :
    (foldedAssign (unfoldedAssign rounds assign) c).val = (assign c).val := by
  sorry

/-- Bundle the pointwise roundtrip into the shuffle equality needed for the
    backward implication of `multiSortable_iff_sortable`. -/
theorem foldedAssign_unfoldedAssign_shuffle {n : Nat} (d : Deck n)
    (rounds : List (List PileType))
    (assign : Fin n → Fin (foldVirtualPileTypesFuture rounds).length) :
    shuffleRound d
      (foldVirtualPileTypesFuture ((unfoldedAssign rounds assign).map (·.types)))
      (foldedAssign (unfoldedAssign rounds assign)) =
    shuffleRound d (foldVirtualPileTypesFuture rounds) assign := by
  sorry

/-- Future-oriented equivalence between multi-round sortability and sortability
    by the folded virtual round.  Forward should use
    `multiShuffleRound_eq_shuffleRound`; backward should use `unfoldedAssign`
    together with the roundtrip lemmas above. -/
theorem multiSortable_iff_sortable {n : Nat} (d : Deck n)
    (rounds : List (List PileType)) :
    MultiSortable d rounds ↔ Sortable d (foldVirtualPileTypesFuture rounds) := by
  sorry
