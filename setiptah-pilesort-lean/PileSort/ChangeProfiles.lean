/-
  Change profiles: labelling a sequence by ascent/descent at consecutive pairs.

  This file currently holds the list-level definition.  The deck-level
  `Deck.changeProfile` and the `deckOfWord` construction (its inverse) will
  migrate here in a later step.
-/
import PileSort.PileShuffle

/-- The change profile of a sequence: label each consecutive pair as ascent (.a)
    or descent (.d).  Requires Nodup to guarantee no ties; the equal branch is
    unreachable. -/
def changeProfile {n : Nat} (l : List (Fin n)) (_ : l.Nodup) : List Action :=
  (l.zip l.tail).map fun (x, y) =>
    if x < y then .a
    else if y < x then .d
    else unreachable!
