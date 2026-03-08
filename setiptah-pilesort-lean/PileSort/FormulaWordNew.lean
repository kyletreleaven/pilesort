/-
  Direct inductive proof of formulaWord_correct using clauseWord consumption forms.

  ## Goal

  Replace FormulaWord.lean's formulaState machinery with a compact induction
  driven by three consumption corollaries for `clauseWord n c ++ NEXT` on the
  replicated-types machine `vpt (vpt ALIGN xs) (replicate m Q)`.

  ## The three corollaries

  All three consume exactly one replication, leaving `m - 1` copies:

  **1. Sat (from START_POS, satisfying assignment exists):** DONE
  `clauseNext_good_consumption` (proved below):
    applyWord (clauseWord n c ++ NEXT ++ suffix) (compile (vpt (vpt ALIGN xs) (replicate m Q))) START_POS
    = xs.length * m + applyWord suffix (compile (vpt (vpt ALIGN xs) (replicate (m-1) Q))) START_POS

  **2. Nonsat (from START_POS, no satisfying assignment):** DONE
  `clauseNext_bad_consumption` (to be proved):
    applyWord (clauseWord n c ++ NEXT ++ suffix) (compile (vpt (vpt ALIGN xs) (replicate m Q))) START_POS
    ≥ xs.length * m + applyWord suffix (compile (vpt (vpt ALIGN xs) (replicate (m-1) Q))) CHAIN_DISQ

  **3. Chain (from any s ≥ CHAIN_DISQ, no clause condition):** TODO
  `clauseNext_chain_consumption` (to be proved, using clauseWord_chain_consumption):
    CHAIN_DISQ ≤ s →
    applyWord (clauseWord n c ++ NEXT ++ suffix) (compile (vpt (vpt ALIGN xs) (replicate m Q))) s
    ≥ xs.length * m + applyWord suffix (compile (vpt (vpt ALIGN xs) (replicate (m-1) Q))) CHAIN_DISQ

  Each follows the same 4-step pattern:
  (a) convert replicated → flat via virtualPileTypes_replicate_Q_comp,
  (b) apply the flat clauseWord consumption lemma,
  (c) handle NEXT (exact via next_correct, or monotone via applyWord_ge),
  (d) virtualPileTypes_append + applyWord_compile_append_shift to shift past the
      xs block, then ← virtualPileTypes_replicate_Q_comp to recover types'.

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

/-- Consumption form: clauseWord ++ NEXT with satisfying assignment consumes one
    block and hands the suffix the remaining replicates at START_POS. -/
theorem clauseNext_good_consumption (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat) (suffix : List Action)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1) (hm : m ≥ 2)
    (vars : List Bool) (hvars : vars.length = n)
    (hxs : xs = embedVars vars ++ [PileType.Q])
    (hsat : satisfiesClause vars c) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)
    let types' := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (m - 1) .Q)
    applyWord (clauseWord n c ++ NEXT ++ suffix) (compile types) START_POS =
      xs.length * ALIGN.length +
        applyWord suffix (compile types') START_POS := by
  simp only []
  rw [applyWord_append, applyWord_append]
  -- (a) convert replicated → flat via virtualPileTypes_replicate_peel
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten) :=
    virtualPileTypes_replicate_peel ALIGN xs m (by omega)
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have hxs_ne : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    match m, hm with
    | m' + 2, _ => simp [List.replicate_succ, List.flatten_cons, hxs_ne]
  rw [h_eq]
  -- (b) apply clauseWord_start_sat on flat machine
  have hcw : applyWord (clauseWord n c)
      (compile (virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten))) START_POS =
      END_POS + n * ALIGN.length :=
    clauseWord_start_sat n c xs _ hn hxs_len hA2 vars hvars hxs hsat
  rw [hcw]
  -- (c) apply next_correct on flat machine
  have hk : n < (xs ++ (List.replicate (m - 1) xs).flatten).length := by simp; omega
  rw [next_correct (xs ++ (List.replicate (m - 1) xs).flatten) n hk, hxs_len]
  -- (d) shift suffix past xs block, then convert A2 back to types'
  rw [show START_POS + (n + 1) * ALIGN.length =
      (virtualPileTypes ALIGN xs).length + START_POS from by
        rw [virtualPileTypes_length, hxs_len]; omega,
      virtualPileTypes_append,
      applyWord_compile_append_shift suffix (virtualPileTypes ALIGN xs) _ START_POS,
      virtualPileTypes_length, hxs_len, ← virtualPileTypes_replicate_Q_comp]

/-- Consumption form: clauseWord ++ NEXT without satisfying assignment reaches
    penalty zone. Suffix sees remaining replicates from CHAIN_DISQ. -/
theorem clauseNext_bad_consumption (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat) (suffix : List Action)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1) (hm : m ≥ 2)
    (hno : ¬ HasMatchingAssignment n xs (satisfiesClause · c)) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)
    let types' := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (m - 1) .Q)
    applyWord (clauseWord n c ++ NEXT ++ suffix) (compile types) START_POS ≥
      xs.length * ALIGN.length +
        applyWord suffix (compile types') CHAIN_DISQ := by
  simp only []
  -- Split word
  rw [applyWord_append, applyWord_append]
  -- (a) clauseWord ≥ bound on replicated machine via flat conversion
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have hxs_ne : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    match m, hm with
    | m' + 2, _ => simp [List.replicate_succ, List.flatten_cons, hxs_ne]
  have h_cw : applyWord (clauseWord n c)
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)))
      START_POS ≥ CHAIN_DISQ + xs.length * ALIGN.length := by
    rw [virtualPileTypes_replicate_peel ALIGN xs m (by omega)]
    have h := clauseWord_start_nonsat n c xs _ hn hxs_len hA2 hno
    rw [hxs_len]; exact h
  have h_mono := applyWord_mono suffix
    (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q))
    (Nat.le_trans h_cw
      (applyWord_ge NEXT (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)) _))
  -- Evaluate the lower bound via decomposition + shift
  have h_len : (virtualPileTypes ALIGN xs).length = xs.length * ALIGN.length :=
    virtualPileTypes_length ALIGN xs
  have h_shift : applyWord suffix
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)))
      (CHAIN_DISQ + xs.length * ALIGN.length) =
      xs.length * ALIGN.length +
        applyWord suffix
          (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (m - 1) .Q)))
          CHAIN_DISQ := by
    rw [virtualPileTypes_replicate_Q_cons _ _ (by omega : m ≥ 1),
        show CHAIN_DISQ + xs.length * ALIGN.length =
          (virtualPileTypes ALIGN xs).length + CHAIN_DISQ from by rw [h_len]; omega,
        applyWord_compile_append_shift, h_len]
  rw [h_shift] at h_mono
  exact h_mono
