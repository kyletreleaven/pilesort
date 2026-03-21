/-
  Multi-round pile shuffle.

  A `ShuffleSpec n` bundles a pile-type list with a deal assignment for one
  round.  `multiShuffleRound` applies a sequence of specs to a deck via
  `shuffleRound`, folding left.

  Note: reversing a pile index (m - 1 - x) is `Fin.rev` from core Lean.
-/
import PileSort.PileShuffle

/-- One round's worth of pile-shuffle parameters. -/
structure ShuffleSpec (n : Nat) where
  types  : List PileType
  assign : Fin n → Fin types.length

/-- Apply a sequence of shuffle rounds to a deck, left to right. -/
def multiShuffleRound {n : Nat} (d : Deck n) (rounds : List (ShuffleSpec n)) : Deck n :=
  rounds.foldl (fun acc r => shuffleRound acc r.types r.assign) d
