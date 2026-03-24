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
  3. Rebuild the local equivalence theorems against the new orientation.

  The goal is to keep names natural in this file and switch over later at the
  module/import boundary once the redesign is stable.
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
