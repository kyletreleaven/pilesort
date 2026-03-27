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

/-- Fold many shuffle specs into one combined spec, in current/future
    orientation. -/
def foldedSpec {n : Nat} : List (ShuffleSpec n) → ShuffleSpec n
  | [] =>
      { types := [PileType.Q]
        assign := fun _ => ⟨0, by simp⟩ }
  | current :: future => combinedSpec current (foldedSpec future)

/-- Unfold a combined spec by splitting off the current round and recurring on
    the future suffix. -/
def unfoldedSpec {n : Nat} :
    (rounds : List (List PileType)) →
    (spec : ShuffleSpec n) →
    spec.types = foldVirtualPileTypesFuture rounds →
    List (ShuffleSpec n)
  | [], _, _ => []
  | current :: future, spec, h =>
      let split := splitSpec spec current (foldVirtualPileTypesFuture future)
        (by simpa [foldVirtualPileTypesFuture] using h)
      split.1 :: unfoldedSpec future split.2 rfl

/-- One-step equation for the future-oriented pile-type fold.
    This is just the defining equation (`rfl`), recorded only as a named rewrite
    rule in case later proofs read more clearly using it explicitly. -/
theorem foldVirtualPileTypesFuture_cons (current : List PileType)
    (future : List (List PileType)) :
    foldVirtualPileTypesFuture (current :: future) =
    virtualPileTypes current (foldVirtualPileTypesFuture future) := by
  rfl

/-- Critical forward composition theorem for the future-oriented fold:
    executing many rounds left-to-right equals one round on the folded future
    spec. -/
theorem multiShuffleRound_eq_shuffleRound {n : Nat} (d : Deck n)
    (specs : List (ShuffleSpec n)) :
    let spec := foldedSpec specs
    multiShuffleRound d specs = shuffleRound d spec.types spec.assign := by
  sorry

/-- Spec-level left inverse: unfolding a combined spec against the intended
    round list and then folding the recovered specs should give back the
    original combined spec. -/
theorem foldedSpec_unfoldedSpec {n : Nat}
    (rounds : List (List PileType))
    (spec : ShuffleSpec n)
    (h : spec.types = foldVirtualPileTypesFuture rounds) :
    foldedSpec (unfoldedSpec rounds spec h) = spec := by
  sorry

/-- Future-oriented equivalence between multi-round sortability and sortability
    by the folded virtual round.  Forward should use
    `multiShuffleRound_eq_shuffleRound`; backward should use `unfoldedAssign`
    together with the roundtrip lemmas above. -/
theorem multiSortable_iff_sortable {n : Nat} (d : Deck n)
    (rounds : List (List PileType)) :
    MultiSortable d rounds ↔ Sortable d (foldVirtualPileTypesFuture rounds) := by
  sorry
