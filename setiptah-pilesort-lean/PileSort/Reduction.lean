/-
  SAT-to-pile-sort reduction: data types and embedding functions.
-/
import PileSort.Automata
import PileSort.Basic
import PileSort.Mono
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
    -- From START_POS with satisfying assignment: → END_POS
    (∀ vars : List Bool, vars.length = n → A1 = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars clause →
      applyWord (clauseWord n clause) (compile types) (START_POS + k * m) =
        END_POS + (k + n) * m)
    ∧
    -- From START_POS without any satisfying assignment matching A1: → penalty
    (¬ (∃ vars : List Bool, vars.length = n ∧ A1 = embedVars vars ++ [PileType.Q]
        ∧ satisfiesClause vars clause) →
      applyWord (clauseWord n clause) (compile types) (START_POS + k * m) ≥
        CHAIN_DISQ + (k + n + 1) * m)
    ∧
    -- From CHAIN_DISQ: penalty propagates unconditionally
    applyWord (clauseWord n clause) (compile types) (CHAIN_DISQ + k * m) ≥
      CHAIN_DISQ + (k + n + 1) * m := by
  sorry

/-- A compiled machine accepts a word if starting from state 0
    it does not reach the sink state (types.length). -/
def accepts (types : List PileType) (word : List Action) : Prop :=
  applyWord word (compile types) 0 < types.length

/-- A formula (conjunction of clauses) is satisfied if every clause is satisfied. -/
def satisfiesFormula (vars : List Bool) (clauses : List Clause) : Prop :=
  ∀ clause ∈ clauses, satisfiesClause vars clause

/-- Forward direction: a satisfying assignment implies acceptance. -/
theorem formulaWord_forward (n : Nat) (clauses : List Clause)
    (xs : List PileType) (vars : List Bool)
    (hxs_len : xs.length = n + 1)
    (hn : vars.length = n)
    (hxs : xs = embedVars vars ++ [PileType.Q])
    (hsat : satisfiesFormula vars clauses)
    (hne : clauses ≠ []) :
    let types := virtualPileTypes
        (virtualPileTypes ALIGN xs)
        (List.replicate clauses.length PileType.Q)
    accepts types (formulaWord n clauses) := by
  sorry

/-- On extended types (one extra block), if no satisfying assignment exists,
    the formulaWord sends state 0 past the original types boundary.
    The vestigial block ensures clauseWord_correct part 3 always has room. -/
theorem formulaWord_penalty_ext (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hxs_len : xs.length = n + 1)
    (hno : ¬ (∃ vars : List Bool, vars.length = n
        ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesFormula vars clauses)) :
    let types_ext := virtualPileTypes ALIGN
        (List.replicate (clauses.length + 1) xs).flatten
    applyWord (formulaWord n clauses) (compile types_ext) 0 ≥
      CHAIN_DISQ + clauses.length * xs.length * ALIGN.length := by
  sorry

/-- Formula-level correctness: a machine compiled from virtualPileTypes ALIGN xs,
    replicated over m clauses, accepts formulaWord n clauses iff
    xs = embedVars(vars) ++ [Q] for some assignment vars satisfying the formula. -/
theorem formulaWord_correct (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hxs_len : xs.length = n + 1)
    (hne : clauses ≠ []) :
    let types := virtualPileTypes
        (virtualPileTypes ALIGN xs)
        (List.replicate clauses.length PileType.Q)
    accepts types (formulaWord n clauses) ↔
      ∃ vars : List Bool, vars.length = n
        ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesFormula vars clauses := by
  intro types
  constructor
  · -- Backward: accepts → ∃ satisfying vars
    -- Contrapositive: apply formulaWord_penalty_ext on extended types,
    -- then applyWord_append_truncate to get result on original types = types.length,
    -- contradicting accepts < types.length.
    sorry
  · -- Forward: ∃ satisfying vars → accepts
    intro ⟨vars, hn, hxs, hsat⟩
    exact formulaWord_forward n clauses xs vars hxs_len hn hxs hsat hne
