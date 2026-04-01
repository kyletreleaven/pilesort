/-
  Gadget word constants and state position constants.

  Mirrors words.py. Each word is a `List Action` used to drive one of the
  reduction gadgets.
-/
import PileSort.Basic
import PileSort.MatchingChain

open PileType in
def ALIGN : List PileType := [Q, Q, Q, Q, S, S]

-- Helper for writing long action words as strings over `a`/`d`.
def toActions : List Char → List Action
  | [] => []
  | 'a' :: rest => .a :: toActions rest
  | _ :: rest => .d :: toActions rest

open Action

-- Moves to the non-activated state on the first-variable block of the current clause segment.
def START_CLAUSE : List Action := [d, a, a, a, a, d, d, a]

-- Administers a positive-literal test for the variable represented by the current block.
def POS : List Action := [a, a, d, d, d, d, a, d, a, a, a, d, a, d]

-- Administers a negative-literal test for the variable represented by the current block.
def NEG : List Action := [d, a, d, d, d, d, a, d, a, a, a, d, a, d]

-- Administers a don't-care test for the variable represented by the current block.
def DK : List Action := [a, d, a, d, d, d, a, d, a, a, a, d, a, d]

-- Administers the final positive-literal test in the current clause segment.
def ENDPOS : List Action := toActions "aaddddaddddaaaaddaaaadddda".toList

-- Administers the final negative-literal test in the current clause segment.
def ENDNEG : List Action := toActions "daddddaddddadaaadaaaadaaaadddda".toList

-- Administers the final don't-care test in the current clause segment.
def ENDDK : List Action := toActions "daaddddaddddaaaaddaaaadddda".toList

-- Single-step transition to the next gadget position.
-- Moves from the end of one clause segment to the beginning of the next.
def NEXT : List Action := [Action.a]

-- Control word that penalizes a block not produced by a Q.
def FORCEQ : List Action := toActions "dadaaaadaaaaddddaaaa".toList

-- Code word used to pass state unaltered from block to block.
def PASS_CODE : List Action := toActions "daaaadadadadddda".toList

-- Long control word used by the alignment gadget.
def ALIGNMENT_CODE : List Action := toActions
  ("aaaaaaaaaaaaaaaaaaaaaaaadaaaaaaaaaaaaaaaa" ++
   "daaaaaaaaaaaaaaaaaadaaaaaaaaaaaaaaaaaadd" ++
   "ddddddddddddddddddadddddaaaaaaaaaaaaaaaa" ++
   "adaaaaadddddddddddadddddaddddaddddaaaa").toList

-- State position constants

-- The natural starting point (first position) on any block
def START_POS : Nat := 0
-- A disqualifying position for the whole chain gadget, corresponding to
-- formula-level non-satisfiability.
def CHAIN_DISQ : Nat := 1
-- The activated clause-test state on a block.
def ACTD : Nat := 2
-- The non-activated clause-test state on a block.
def NACTD : Nat := 3
-- The natural end position on a block; on a terminal variable block this is the
-- successful exit position.
def END_POS : Nat := 5
-- The same numeric position as `END_POS`, but interpreted on clause-sentinel
-- blocks as the clause-disqualification position.
def CLAUSE_DISQ : Nat := 5
