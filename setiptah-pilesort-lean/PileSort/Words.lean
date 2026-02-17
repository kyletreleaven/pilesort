/-
  Gadget word constants and state position constants.

  Mirrors words.py. Each word is a List Action.
  In the paper, R maps to Action.a (advance) and L maps to Action.d (descend).
-/
import PileSort.Basic

open PileType in
def ALIGN : List PileType := [Q, Q, Q, Q, S, S]

-- Helper to convert a paper-notation string (R/L) to a list of actions.
-- Used for long words to avoid tedious manual transcription.
def toActions : List Char → List Action
  | [] => []
  | 'R' :: rest => .a :: toActions rest
  | _ :: rest => .d :: toActions rest    -- L (and anything else) → d

open Action

-- START_CLAUSE = path_from_string('LRRRRLLR')
-- L→d R→a R→a R→a R→a L→d L→d R→a
def START_CLAUSE : List Action := [d, a, a, a, a, d, d, a]

-- POS = path_from_string('RRLLLLRLRRRLRL')
-- R→a R→a L→d L→d L→d L→d R→a L→d R→a R→a R→a L→d R→a L→d
def POS : List Action := [a, a, d, d, d, d, a, d, a, a, a, d, a, d]

-- NEG = path_from_string('LRLLLLRLRRRLRL')
-- L→d R→a L→d L→d L→d L→d R→a L→d R→a R→a R→a L→d R→a L→d
def NEG : List Action := [d, a, d, d, d, d, a, d, a, a, a, d, a, d]

-- DK = path_from_string('RLRLLLRLRRRLRL')
-- R→a L→d R→a L→d L→d L→d R→a L→d R→a R→a R→a L→d R→a L→d
def DK : List Action := [a, d, a, d, d, d, a, d, a, a, a, d, a, d]

-- ENDPOS = path_from_string('RRLLLLRLLLLRRRRLLRRRRLLLLR')
def ENDPOS : List Action := toActions "RRLLLLRLLLLRRRRLLRRRRLLLLR".toList

-- ENDNEG = path_from_string('LRLLLLRLLLLRLRRRLRRRRLRRRRLLLLR')
def ENDNEG : List Action := toActions "LRLLLLRLLLLRLRRRLRRRRLRRRRLLLLR".toList

-- ENDDK = path_from_string('LRRLLLLRLLLLRRRRLLRRRRLLLLR')
def ENDDK : List Action := toActions "LRRLLLLRLLLLRRRRLLRRRRLLLLR".toList

-- NEXT = path_from_string("R")
def NEXT : List Action := [Action.a]

-- FORCEQ = path_from_string("LRLRRRRLRRRRLLLLRRRR")
def FORCEQ : List Action := toActions "LRLRRRRLRRRRLLLLRRRR".toList

-- PASS_CODE = path_from_string("LRRRRLRLRLRLLLLR")
def PASS_CODE : List Action := toActions "LRRRRLRLRLRLLLLR".toList

-- ALIGNMENT_CODE = path_from_string('RRRR...RRRR') (162 actions)
def ALIGNMENT_CODE : List Action := toActions
  ("RRRRRRRRRRRRRRRRRRRRRRRRLRRRRRRRRRRRRRRR" ++
   "RRRLRRRRRRRRRRRRRRRRRRLRRRRRRRRRRRRRRRRR" ++
   "RLLLLLLLLLLLLLLLLLLLLLRLLLLLRRRRRRRRRRRR" ++
   "RRRRRLRRRRRLLLLLLLLLLLRLLLLLRLLLLRLLLLRR" ++
   "RR").toList

-- State position constants
def START_POS : Nat := 0
def CHAIN_DISQ : Nat := 1
def ACTD : Nat := 2
def NACTD : Nat := 3
def END_POS : Nat := 5
def CLAUSE_DISQ : Nat := 5
