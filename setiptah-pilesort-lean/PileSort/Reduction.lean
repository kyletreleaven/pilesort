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

/-- A compiled machine accepts a word if starting from state 0
    it does not reach the sink state (types.length). -/
def accepts (types : List PileType) (word : List Action) : Prop :=
  applyWord word (compile types) 0 < types.length

/-- A formula (conjunction of clauses) is satisfied if every clause is satisfied. -/
def satisfiesFormula (vars : List Bool) (clauses : List Clause) : Prop :=
  ∀ clause ∈ clauses, satisfiesClause vars clause

/-- Tail-recursive computation of the formulaWord endpoint, specialized for
    the clause-by-clause structure. At each level, the types have
    `clauses_.length + 2` Q-replications (remaining + last + vestigial).
    The recursive case peels off one clause, accumulating one block's worth
    of offset via the shift property of `compile_append_right`. -/
def formulaState (n : Nat) (xs : List PileType)
    (clauses_ : List Clause) (last : Clause) (start : Nat) : Nat :=
  let types := virtualPileTypes (virtualPileTypes ALIGN xs)
      (List.replicate (clauses_.length + 2) .Q)
  let block := xs.length * ALIGN.length
  match clauses_ with
  | [] => applyWord (clauseWord n last) (compile types) start
  | c :: rest =>
    block + formulaState n xs rest last
      (applyWord (clauseWord n c ++ NEXT) (compile types) start - block)
