/-
  Virtual pile type composition for multi-round pile shuffle.

  Mirrors multiround.py:
    virtual_pile_types(pt1, pt2) composes two rounds of pile types
    into equivalent single-round virtual pile types.

  Q acts as identity on the pile type sequence.
  S reverses and inverts all types (Q↔S).
-/
import PileSort.Basic

def invertType : PileType → PileType
  | .Q => .S
  | .S => .Q

def applyStack (pileTypes : List PileType) : List PileType :=
  (pileTypes.reverse).map invertType

def applyPile (pileType : PileType) (pileTypes : List PileType) : List PileType :=
  match pileType with
  | .Q => pileTypes
  | .S => applyStack pileTypes

/-- Compose two rounds of pile types into a single-round virtual pile type sequence.

    For each type t in pt2, expand it via applyPile into a sub-sequence,
    then concatenate all sub-sequences. -/
def virtualPileTypes (pt1 pt2 : List PileType) : List PileType :=
  pt2.bind (fun typ => applyPile typ pt1)
