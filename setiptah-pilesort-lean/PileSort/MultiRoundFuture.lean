import PileSort.MultiRound

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

  1. Reorient virtual-pile folding so the recursive equation is on
     `current :: future`, with the accumulated term interpreted as the effect of
     future rounds.
  2. Reorient `combinedAssign` / `splitAssign` to match that same semantic
     direction.
  3. Reorient `foldedAssign` to match the new fold direction.
  4. Redefine `unfoldedAssign` in the same direction, so its main equation is a
     direct computation rule instead of a transport lemma.
  5. Reprove `multiShuffleRound_eq_shuffleRound` and
     `multiSortable_iff_sortable` against the new orientation.
  The goal is to keep names natural in this file and switch over later at the
  module/import boundary once the redesign is stable.
-/
