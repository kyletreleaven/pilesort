/-
  The top-level correctness theorem for the SAT-to-pile-sort reduction:
  `formulaWord_correct` states that the pile-sort machine compiled from
  `virtualPileTypes ALIGN xs` accepts `formulaWord n clauses` if and only if
  there exists an assignment satisfying the formula.  This is the main result
  of the reduction.
-/
import PileSort.Mono
import PileSort.Reduction
-- import PileSort.ClauseWord
import PileSort.Reduction.SATToMatchingChain.Gadgets.Next
import PileSort.FormulaWordNew

/-- Sat form: formulaWord from START_POS reaches exact position when vars satisfies the formula.
    Proved by induction on clauses_ using clauseNext_good_consumption (step) and
    clauseWord_start_consumption sat branch (base). -/
theorem formulaWord_from_start_sat' (n : Nat) (clauses_ : List Clause) (last : Clause)
    (xs : List PileType) (vars : List Bool)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hvars : vars.length = n)
    (hxs : xs = embedVars vars ++ [PileType.Q])
    (hsat : satisfiesFormula vars (clauses_ ++ [last])) :
    applyWord (formulaWord n (clauses_ ++ [last]))
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
        (List.replicate (clauses_.length + 2) .Q))) START_POS =
      clauses_.length * (xs.length * ALIGN.length) + END_POS + n * ALIGN.length := by
  induction clauses_ with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_mul, Nat.zero_add]
    have hfw : formulaWord n [last] = clauseWord n last := by
      rw [show [last] = [] ++ [last] from rfl, formulaWord_split]; simp
    rw [hfw, virtualPileTypes_replicate_peel ALIGN xs 2 (by omega)]
    have hxs_ne : xs ≠ [] := by intro h; simp [h] at hxs_len
    have hA2 : (List.replicate 1 xs).flatten ≠ [] := by
      simp [List.replicate_succ, List.flatten_cons, hxs_ne]
    have hsat_last : satisfiesClause vars last := hsat last (by simp)
    have hhas : HasMatchingAssignment n xs (satisfiesClause · last) :=
      ⟨vars, hvars, hxs, hsat_last⟩
    simp only [show (2 : Nat) - 1 = 1 from rfl]
    have h := clauseWord_start_sat_cons n last [] xs _ hn hxs_len hA2 hhas
    have hnil : ∀ (f : Action → Nat → Nat) s, applyWord [] f s = s := fun _ _ => rfl
    simp only [List.append_nil, hnil] at h
    rw [Nat.add_comm] at h; exact h
  | cons c rest ih =>
    simp only [List.length_cons]
    rw [formulaWord_cons]
    have hsat_c : satisfiesClause vars c := hsat c (List.mem_cons_self c _)
    have hsat_rest : satisfiesFormula vars (rest ++ [last]) :=
      fun cl hmem => hsat cl (List.mem_cons_of_mem c hmem)
    have h_good := clauseNext_good_consumption n c xs (rest.length + 3)
      (formulaWord n (rest ++ [last])) hn hxs_len (by omega) vars hvars hxs hsat_c
    simp only [show rest.length + 3 - 1 = rest.length + 2 from by omega] at h_good
    rw [h_good, ih hsat_rest]
    have hfact : (rest.length + 1) * (xs.length * ALIGN.length) =
        xs.length * ALIGN.length + rest.length * (xs.length * ALIGN.length) := by
      rw [show rest.length + 1 = 1 + rest.length from by omega, Nat.add_mul, Nat.one_mul]
    omega

/-- If no assignment satisfies c :: rest but some assignment satisfies c,
    then no assignment satisfies rest (since xs determines vars uniquely
    via embedVars_injective). -/
theorem not_satisfiesFormula_rest (n : Nat) (xs : List PileType)
    (c : Clause) (rest : List Clause)
    (hno : ¬ HasMatchingAssignment n xs (satisfiesFormula · (c :: rest)))
    (hc : HasMatchingAssignment n xs (satisfiesClause · c)) :
    ¬ HasMatchingAssignment n xs (satisfiesFormula · rest) := by
  obtain ⟨vars₀, hvars₀, hxs₀, hsat₀⟩ := hc
  intro ⟨vars', hvars', hxs', hsat'⟩
  have heq : vars' = vars₀ := by
    have : embedVars vars' = embedVars vars₀ := by
      have := hxs₀ ▸ hxs'; simp at this; exact this.symm
    exact embedVars_injective vars' vars₀ this
  subst heq
  exact hno ⟨vars', hvars', hxs', fun cl hmem => by
    cases List.mem_cons.mp hmem with
    | inl h => exact h ▸ hsat₀
    | inr h => exact hsat' cl h⟩

/-- Nonsat form: formulaWord from START_POS reaches the out-of-bounds zone when no assignment
    satisfies the formula. Proved by induction on clauses_ using:
    - clauseWord_start_consumption nonsat branch (base),
    - clauseNext_bad_consumption + formulaWord_chain_pos' (step, c-nonsat),
    - clauseNext_good_consumption + not_satisfiesFormula_rest + IH (step, c-sat). -/
theorem formulaWord_from_start_unsat' (n : Nat) (clauses_ : List Clause) (last : Clause)
    (xs : List PileType)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hno : ¬ HasMatchingAssignment n xs (satisfiesFormula · (clauses_ ++ [last]))) :
    applyWord (formulaWord n (clauses_ ++ [last]))
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
        (List.replicate (clauses_.length + 2) .Q))) START_POS ≥
      (clauses_.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
  induction clauses_ with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_add, Nat.one_mul]
    have hfw : formulaWord n [last] = clauseWord n last := by
      rw [show [last] = [] ++ [last] from rfl, formulaWord_split]; simp
    rw [hfw, virtualPileTypes_replicate_peel ALIGN xs 2 (by omega)]
    simp only [show (2 : Nat) - 1 = 1 from rfl, List.replicate_succ, List.replicate_zero,
               List.flatten_cons, List.flatten_nil, List.append_nil]
    have hxs_ne : xs ≠ [] := by intro h; simp [h] at hxs_len
    have hno_last : ¬ HasMatchingAssignment n xs (satisfiesClause · last) := by
      intro ⟨vars, hvars, hxs', hsat'⟩
      exact hno ⟨vars, hvars, hxs', by simp [satisfiesFormula, hsat']⟩
    have h := clauseWord_start_nonsat_cons n last [] xs xs hn hxs_len hxs_ne hno_last
    have hnil : ∀ (f : Action → Nat → Nat) s, applyWord [] f s = s := fun _ _ => rfl
    simp only [List.append_nil, hnil] at h
    rw [hxs_len]; omega
  | cons c rest ih =>
    simp only [List.length_cons, show rest.length + 1 + 2 = rest.length + 3 from by omega]
    rw [formulaWord_cons]
    have hfact : (rest.length + 1 + 1) * (xs.length * ALIGN.length) =
        xs.length * ALIGN.length + (rest.length + 1) * (xs.length * ALIGN.length) := by
      rw [show rest.length + 1 + 1 = 1 + (rest.length + 1) from by omega, Nat.add_mul, Nat.one_mul]
    rcases Classical.em (HasMatchingAssignment n xs (satisfiesClause · c)) with hc | hc
    · -- c-sat: clauseNext_good_consumption, then IH Lemma 2 for rest ++ [last]
      obtain ⟨vars', hvars', hxs', hsat_c⟩ := hc
      have h_good := clauseNext_good_consumption n c xs (rest.length + 3)
        (formulaWord n (rest ++ [last])) hn hxs_len (by omega) vars' hvars' hxs' hsat_c
      simp only [show rest.length + 3 - 1 = rest.length + 2 from by omega] at h_good
      rw [h_good]
      have hno' : ¬ HasMatchingAssignment n xs (satisfiesFormula · (rest ++ [last])) :=
        not_satisfiesFormula_rest n xs c (rest ++ [last]) hno ⟨vars', hvars', hxs', hsat_c⟩
      have h_ih := ih hno'
      omega
    · -- c-nonsat: clauseNext_bad_consumption, then formulaWord_chain_pos'
      have h_bad := clauseNext_bad_consumption n c xs (rest.length + 3)
        (formulaWord n (rest ++ [last])) hn hxs_len (by omega) hc
      simp only [show rest.length + 3 - 1 = rest.length + 2 from by omega] at h_bad
      have h_chain := formulaWord_chain_pos' n rest last xs CHAIN_DISQ hn hxs_len (by omega)
      omega

/-- accepts on types is equivalent to applyWord on extended types being < types.length. -/
theorem accepts_iff_applyWord_contained (word : List Action) (types extra : List PileType) :
    accepts types word ↔
      applyWord word (compile (types ++ extra)) 0 < types.length := by
  unfold accepts
  rw [applyWord_append_truncate word types extra 0 (Nat.zero_le _)]
  simp only [Nat.min_def]; split <;> omega

/-- Formula-level correctness (decomposed form): takes clauses as init ++ [last]. -/
theorem formulaWord_correct' (n : Nat) (clauses_ : List Clause) (last : Clause)
    (xs : List PileType)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1) :
    let types := virtualPileTypes
        (virtualPileTypes ALIGN xs)
        (List.replicate (clauses_.length + 1) PileType.Q)
    accepts types (formulaWord n (clauses_ ++ [last])) ↔
      HasMatchingAssignment n xs (satisfiesFormula · (clauses_ ++ [last])) := by
  intro types
  rw [accepts_iff_applyWord_contained _ _ (virtualPileTypes ALIGN xs),
      ← virtualPileTypes_replicate_Q_snoc,
      show clauses_.length + 1 + 1 = clauses_.length + 2 from by omega,
      show (0 : Nat) = START_POS from rfl]
  have h_len : types.length = (clauses_.length + 1) * (xs.length * ALIGN.length) := by
    rw [virtualPileTypes_replicate_Q_length, virtualPileTypes_length]
  constructor
  · -- Backward: applyWord < length → HasMatchingAssignment
    intro h
    exact Classical.byContradiction fun hno => by
      have := formulaWord_from_start_unsat' n clauses_ last xs hn hxs_len hno
      rw [h_len] at h; unfold CHAIN_DISQ at this; omega
  · -- Forward: HasMatchingAssignment → applyWord < length
    intro ⟨vars, hvars, hxs, hsat⟩
    rw [formulaWord_from_start_sat' n clauses_ last xs vars hn hxs_len hvars hxs hsat, h_len,
        show (clauses_.length + 1) * (xs.length * ALIGN.length) =
          clauses_.length * (xs.length * ALIGN.length) + xs.length * ALIGN.length from by
          rw [Nat.add_mul, Nat.one_mul], hxs_len]
    unfold END_POS ALIGN; simp; omega

/-- Formula-level correctness: a machine compiled from virtualPileTypes ALIGN xs,
    replicated over m clauses, accepts formulaWord n clauses iff
    xs = embedVars(vars) ++ [Q] for some assignment vars satisfying the formula. -/
theorem formulaWord_correct (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hne : clauses ≠ []) :
    accepts
      (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate clauses.length PileType.Q))
      (formulaWord n clauses)
    ↔ HasMatchingAssignment n xs (satisfiesFormula · clauses) := by
  obtain ⟨init, last, rfl, hlen⟩ := list_split_last clauses hne
  simp only [List.length_append, List.length_singleton] at *
  exact formulaWord_correct' n init last xs hn hxs_len
