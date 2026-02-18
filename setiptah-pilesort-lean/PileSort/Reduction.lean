/-
  SAT-to-pile-sort reduction: data types and embedding functions.
-/
import PileSort.Automata
import PileSort.Basic
import PileSort.VirtualPileTypes
import PileSort.Words

inductive Literal where
  | pos (var : Nat)
  | neg (var : Nat)
  deriving DecidableEq, Repr

abbrev Clause := List Literal

/-- The test word for variable i in clause φ_j:
    POS if x_i ∈ φ_j, NEG if ¬x_i ∈ φ_j, DK otherwise. -/
def testWord (i : Nat) (clause : Clause) : List Action :=
  if .pos i ∈ clause then POS
  else if .neg i ∈ clause then NEG
  else DK

/-- The end-test word for variable i in clause φ_j:
    ENDPOS if x_i ∈ φ_j, ENDNEG if ¬x_i ∈ φ_j, ENDDK otherwise. -/
def endTestWord (i : Nat) (clause : Clause) : List Action :=
  if .pos i ∈ clause then ENDPOS
  else if .neg i ∈ clause then ENDNEG
  else ENDDK

/-- Word embedding of a clause over n variables:
    START_CLAUSE ++ test_0(φ) ++ ... ++ test_{n-2}(φ) ++ endtest_{n-1}(φ) -/
def clauseWord (n : Nat) (clause : Clause) : List Action :=
  START_CLAUSE ++
  (List.range (n - 1)).flatMap (fun i => testWord i clause) ++
  endTestWord (n - 1) clause

/-- Word embedding of a formula (list of clauses) over n variables:
    clause(φ_0) ++ NEXT ++ clause(φ_1) ++ NEXT ++ ... ++ clause(φ_{m-1}) -/
def formulaWord (n : Nat) (clauses : List Clause) : List Action :=
  (clauses.flatMap (fun c => clauseWord n c ++ NEXT)).dropLast

/-- A clause is satisfied by a variable assignment if some literal matches. -/
def satisfiesClause (vars : List Bool) (clause : Clause) : Prop :=
  ∃ l ∈ clause, match l with
    | .pos i => vars.getD i false = true
    | .neg i => vars.getD i false = false

/-- Clause word correctness for machine compiled from virtualPileTypes ALIGN (A0 ++ A1 ++ A2)
    where A1 has length n+1. -/
theorem clauseWord_correct (n : Nat) (clause : Clause)
    (A0 A1 A2 : List PileType)
    (hA1 : A1.length = n + 1) :
    let types := virtualPileTypes ALIGN (A0 ++ A1 ++ A2)
    let k := A0.length
    let m := ALIGN.length
    -- From START_POS: if ∃ vars satisfying clause with A1 = embedVars(vars) ++ [Q],
    --   then → END_POS; otherwise → penalty
    (if ∃ vars : List Bool, vars.length = n ∧ A1 = embedVars vars ++ [PileType.Q]
                            ∧ satisfiesClause vars clause
     then applyWord (clauseWord n clause) (compile types) (START_POS + k * m) =
            END_POS + (k + n) * m
     else applyWord (clauseWord n clause) (compile types) (START_POS + k * m) ≥
            CHAIN_DISQ + (k + n + 1) * m)
    ∧
    -- From CHAIN_DISQ: penalty propagates unconditionally
    applyWord (clauseWord n clause) (compile types) (CHAIN_DISQ + k * m) ≥
      CHAIN_DISQ + (k + n + 1) * m := by
  sorry
