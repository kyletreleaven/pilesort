/-
  Consumption-form corollaries for `clauseWord n c ++ NEXT` on the replicated-types
  machine `virtualPileTypes (virtualPileTypes ALIGN xs) (replicate m Q)`.  These are
  the inductive engine used by `FormulaWord.lean` to prove `formulaWord_correct`.

  Each corollary consumes exactly one replication of `xs`, leaving `m - 1` copies:

  - **`clauseNext_good_consumption`**: satisfying assignment exists → lands at START_POS.
  - **`clauseNext_bad_consumption`**: no satisfying assignment → reaches penalty zone (≥ CHAIN_DISQ).
  - **`clauseNext_chain_consumption`**: from any s ≥ CHAIN_DISQ, unconditionally → ≥ CHAIN_DISQ.

  Also contains **`formulaWord_chain_pos'`**: the chain lemma lifted to full formulaWord
  sequences, used in the nonsat inductive case of `formulaWord_from_start_unsat'`.
-/
import PileSort.Reduction.SATToMatchingChain.ClauseWord
import PileSort.Reduction.SATToMatchingChain.Gadgets.Next

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
  -- (b) apply clauseWord_start_sat_cons (empty suffix) on flat machine
  have hcw : applyWord (clauseWord n c)
      (compile (virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten))) START_POS =
      END_POS + n * ALIGN.length := by
    have h := clauseWord_start_sat_cons n c [] xs _ hn hxs_len hA2 ⟨vars, hvars, hxs, hsat⟩
    have hnil : ∀ (f : Action → Nat → Nat) s, applyWord [] f s = s := fun _ _ => rfl
    simp only [List.append_nil, hnil] at h; omega
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
    have h := clauseWord_start_nonsat_cons n c [] xs _ hn hxs_len hA2 hno
    have hnil : ∀ (f : Action → Nat → Nat) s, applyWord [] f s = s := fun _ _ => rfl
    simp only [List.append_nil, hnil] at h; rw [hxs_len]; omega
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

/-- Consumption form: clauseWord ++ NEXT from any s ≥ CHAIN_DISQ (no clause condition).
    Suffix sees remaining replicates from CHAIN_DISQ. -/
theorem clauseNext_chain_consumption (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat) (suffix : List Action) (s : Nat)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1) (hm : m ≥ 2)
    (hs : CHAIN_DISQ ≤ s) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)
    let types' := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (m - 1) .Q)
    applyWord (clauseWord n c ++ NEXT ++ suffix) (compile types) s ≥
      xs.length * ALIGN.length +
        applyWord suffix (compile types') CHAIN_DISQ := by
  simp only []
  rw [applyWord_append, applyWord_append]
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have hxs_ne : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    match m, hm with
    | m' + 2, _ => simp [List.replicate_succ, List.flatten_cons, hxs_ne]
  -- clauseWord from CHAIN_DISQ reaches ≥ CHAIN_DISQ + xs.length * ALIGN.length
  have h_cw : applyWord (clauseWord n c)
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)))
      CHAIN_DISQ ≥ CHAIN_DISQ + xs.length * ALIGN.length := by
    rw [virtualPileTypes_replicate_peel ALIGN xs m (by omega)]
    have h := clauseWord_chain_consumption n c [] xs _ hn hxs_len hA2
    simp only [List.append_nil] at h
    have hnil : applyWord ([] : List Action) (compile (virtualPileTypes ALIGN (List.replicate (m - 1) xs).flatten)) CHAIN_DISQ = CHAIN_DISQ := rfl
    rw [hnil] at h
    rw [hxs_len]
    omega
  -- Monotone in starting state: bound holds from s ≥ CHAIN_DISQ
  have h_cw_s : applyWord (clauseWord n c)
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)))
      s ≥ CHAIN_DISQ + xs.length * ALIGN.length :=
    Nat.le_trans h_cw (applyWord_mono (clauseWord n c) _ hs)
  -- NEXT only increases, suffix is monotone
  have h_mono := applyWord_mono suffix
    (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q))
    (Nat.le_trans h_cw_s
      (applyWord_ge NEXT (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)) _))
  -- Evaluate the lower bound via decomposition + shift (same as clauseNext_bad_consumption)
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

/-- Chain form: formulaWord from any s ≥ CHAIN_DISQ reaches the out-of-bounds zone,
    regardless of clause content. Proved by induction on clauses_ using
    clauseWord_chain_consumption (base) and clauseNext_chain_consumption (step). -/
theorem formulaWord_chain_pos' (n : Nat) (clauses_ : List Clause) (last : Clause)
    (xs : List PileType) (s : Nat)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hs : CHAIN_DISQ ≤ s) :
    applyWord (formulaWord n (clauses_ ++ [last]))
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
        (List.replicate (clauses_.length + 2) .Q))) s ≥
      (clauses_.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
  induction clauses_ generalizing s with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_add, Nat.one_mul]
    have hfw : formulaWord n [last] = clauseWord n last := by
      rw [show [last] = [] ++ [last] from rfl, formulaWord_split]; simp
    rw [hfw, virtualPileTypes_replicate_peel ALIGN xs 2 (by omega)]
    simp only [show (2 : Nat) - 1 = 1 from rfl, List.replicate_succ, List.replicate_zero,
               List.flatten_cons, List.flatten_nil, List.append_nil]
    have hxs_ne : xs ≠ [] := by intro h; simp [h] at hxs_len
    have h := clauseWord_chain_consumption n last [] xs xs hn hxs_len hxs_ne
    simp only [List.append_nil] at h
    have hnil : applyWord ([] : List Action) (compile (virtualPileTypes ALIGN xs)) CHAIN_DISQ
        = CHAIN_DISQ := rfl
    rw [hnil, ← hxs_len] at h
    exact Nat.le_trans h (applyWord_mono _ _ hs)
  | cons c rest ih =>
    simp only [List.length_cons]
    rw [formulaWord_cons]
    have h_chain := clauseNext_chain_consumption n c xs (rest.length + 3)
      (formulaWord n (rest ++ [last])) s hn hxs_len (by omega) hs
    simp only [show rest.length + 3 - 1 = rest.length + 2 from by omega] at h_chain
    have h_ih := ih CHAIN_DISQ (by omega)
    have hfact : (rest.length + 2) * (xs.length * ALIGN.length) =
        xs.length * ALIGN.length + (rest.length + 1) * (xs.length * ALIGN.length) := by
      rw [show rest.length + 2 = 1 + (rest.length + 1) from by omega, Nat.add_mul, Nat.one_mul]
    rw [hfact]
    exact Nat.le_trans (Nat.add_le_add_left h_ih _) h_chain
