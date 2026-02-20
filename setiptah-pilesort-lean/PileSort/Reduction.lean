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

/-- formulaState_eq: The tail-recursive formulaState computation equals
    the direct application of formulaWord to the compiled machine.

    Given clauses = init ++ [last], the types have (init.length + 2)
    Q-replications of the inner block (virtualPileTypes ALIGN xs):
    - init.length blocks for the remaining clauses in init,
    - 1 block for last,
    - 1 vestigial block (so clauseWord_correct part 3 has room).

    The RHS applies the full formulaWord to a single type list.
    The LHS (formulaState) uses shrinking types at each recursive level.
    The shift lemma bridges these views: after clauseWord c ++ NEXT
    advances past the first block (h_advance), we peel off that block
    and recurse on inner types with the remaining formula word. -/
theorem formulaState_eq (n : Nat) (xs : List PileType)
    (init : List Clause) (last : Clause) (start : Nat)
    (h_advance : ∀ (c : Clause) (m : Nat) (s : Nat), m ≥ 2 →
      xs.length * ALIGN.length ≤
        applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
            (List.replicate m .Q))) s) :
    formulaState n xs init last start =
      applyWord (formulaWord n (init ++ [last]))
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
          (List.replicate (init.length + 2) .Q))) start := by
  sorry

theorem formulaWord_split (n : Nat) (init : List Clause) (last : Clause) :
    formulaWord n (init ++ [last]) =
    (init.flatMap (fun c => clauseWord n c ++ NEXT)) ++ clauseWord n last := by
  unfold formulaWord
  rw [List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [← List.append_assoc]
  show ((init.flatMap (fun c => clauseWord n c ++ NEXT)) ++ clauseWord n last ++ NEXT).dropLast =
    (init.flatMap (fun c => clauseWord n c ++ NEXT)) ++ clauseWord n last
  unfold NEXT
  rw [List.dropLast_concat]

private theorem replicate_succ_append {α : Type} (m : Nat) (x : α) :
    List.replicate (m + 1) x = List.replicate m x ++ [x] := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (x :: ·) ih

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
  · -- Backward: accepts → ∃ satisfying vars (contrapositive via penalty_ext + truncation)
    intro hacc
    exact Classical.byContradiction fun hno => by
      have hpen := formulaWord_penalty_ext n clauses xs hxs_len hno
      -- Rewrite types as virtualPileTypes ALIGN (replicate m xs).flatten
      have htypes : types = virtualPileTypes ALIGN (List.replicate clauses.length xs).flatten :=
        virtualPileTypes_replicate_Q_comp ALIGN xs clauses.length
      -- types_ext = types ++ extra
      have hext : virtualPileTypes ALIGN (List.replicate (clauses.length + 1) xs).flatten =
          virtualPileTypes ALIGN (List.replicate clauses.length xs).flatten ++
          virtualPileTypes ALIGN xs := by
        rw [replicate_succ_append, List.flatten_append, virtualPileTypes_append,
            List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [htypes] at hacc; rw [hext] at hpen
      unfold accepts at hacc
      -- Truncation: result on types = min(result on ext, types.length)
      have htrunc := applyWord_append_truncate (formulaWord n clauses)
          (virtualPileTypes ALIGN (List.replicate clauses.length xs).flatten)
          (virtualPileTypes ALIGN xs) 0 (Nat.zero_le _)
      -- types.length ≤ result on ext (since CHAIN_DISQ ≥ 1)
      have hge : (virtualPileTypes ALIGN (List.replicate clauses.length xs).flatten).length ≤
          applyWord (formulaWord n clauses) (compile
            (virtualPileTypes ALIGN (List.replicate clauses.length xs).flatten ++
             virtualPileTypes ALIGN xs)) 0 := by
        have hlen : (virtualPileTypes ALIGN (List.replicate clauses.length xs).flatten).length =
            clauses.length * xs.length * ALIGN.length := by
          rw [virtualPileTypes_length, flatten_replicate_length, Nat.mul_assoc]
        unfold CHAIN_DISQ at hpen; omega
      rw [htrunc, Nat.min_eq_right hge] at hacc
      omega
  · -- Forward: ∃ satisfying vars → accepts
    intro ⟨vars, hn, hxs, hsat⟩
    exact formulaWord_forward n clauses xs vars hxs_len hn hxs hsat hne
