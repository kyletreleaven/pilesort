/-
  Direct inductive proof of formulaWord_correct using clauseWord consumption forms.

  ## Goal

  Replace FormulaWord.lean's formulaState machinery with a compact induction
  driven by three consumption corollaries for `clauseWord n c ++ NEXT` on the
  replicated-types machine `vpt (vpt ALIGN xs) (replicate m Q)`.

  ## The three corollaries

  All three consume exactly one replication, leaving `m - 1` copies:

  **1. Sat (from START_POS, satisfying assignment exists):**
  Already exists as `clauseNext_good_consumption`:
    applyWord (clauseWord n c ++ NEXT ++ suffix) (compile (vpt (vpt ALIGN xs) (replicate m Q))) START_POS
    = xs.length * m + applyWord suffix (compile (vpt (vpt ALIGN xs) (replicate (m-1) Q))) START_POS

  **2. Nonsat (from START_POS, no satisfying assignment):**
  Essentially already `clauseNext_bad_consumption`:
    applyWord (clauseWord n c ++ NEXT ++ suffix) (compile (vpt (vpt ALIGN xs) (replicate m Q))) START_POS
    ≥ xs.length * m + applyWord suffix (compile (vpt (vpt ALIGN xs) (replicate (m-1) Q))) CHAIN_DISQ

  **3. Chain (from any s ≥ CHAIN_DISQ, no clause condition):**
  New lemma, follows from clauseWord_chain_consumption:
    CHAIN_DISQ ≤ s →
    applyWord (clauseWord n c ++ NEXT ++ suffix) (compile (vpt (vpt ALIGN xs) (replicate m Q))) s
    ≥ xs.length * m + applyWord suffix (compile (vpt (vpt ALIGN xs) (replicate (m-1) Q))) CHAIN_DISQ

  Each follows the same 4-step pattern established in clauseNext_good_consumption:
  (a) convert replicated → flat via virtualPileTypes_replicate_Q_comp,
  (b) apply the flat clauseWord consumption lemma,
  (c) handle NEXT (exact via next_correct, or monotone via applyWord_ge),
  (d) peel one block via virtualPileTypes_replicate_Q_cons + applyWord_compile_append_shift.

  ## The direct proof of formulaWord_correct'

  formulaWord_correct' for `clauses_ ++ [last]` on `(clauses_.length + 1)` replications
  is proved by induction on `clauses_`, using the three corollaries above plus
  clauseWord_start_consumption for the last clause:

  **Base case (clauses_ = [], last clause only):**
  Apply clauseWord_start_consumption on the 1-replication machine:
  - Sat:   result = END_POS + n*m < (n+1)*m = block size → in bounds → accepted.
  - Nonsat: result ≥ CHAIN_DISQ + (n+1)*m ≥ block size → out of bounds → rejected.

  **Inductive case (c :: rest ++ [last]):**
  Case split on HasMatchingAssignment for c:
  - Sat:   Apply corollary 1. State resets to START_POS on (m-1) reps. Apply IH.
  - Nonsat: Apply corollary 2. State is ≥ CHAIN_DISQ on (m-1) reps.
            Apply corollary 3 repeatedly (once per remaining init clause).
            Last clause from CHAIN_DISQ via clauseWord_start_consumption nonsat branch
            (or a chain lemma) → out of bounds.

  ## What this eliminates from FormulaWord.lean

  - formulaState and its definition
  - formulaState_eq (connecting formulaState to applyWord formulaWord)
  - formulaState_forward
  - formulaState_penalty
  - formulaState_penalty_start
  - formulaState_penalty_all
  - clauseNext_sat
  - clauseNext_advance
  - not_satisfiesFormula_rest (may still be needed for the sat/nonsat case split)
  - formulaWord_sat_pos / formulaWord_unsat_pos (superseded by direct induction)
  - clauseWord_start_sat_rep, clauseWord_start_nonsat_rep, next_correct_rep
    (baked into the three corollaries)

  ## Open questions

  - Whether `not_satisfiesFormula_rest` survives or is inlined.
  - Whether clauseWord_chain_consumption suffices for corollary 3, or whether
    a small wrapper lemma for the replicated machine is cleaner.
  - Whether clauseWord_penalty can be entirely eliminated once corollary 3 exists.
-/
import PileSort.ClauseWordCorrect
import PileSort.Gadgets.Next
