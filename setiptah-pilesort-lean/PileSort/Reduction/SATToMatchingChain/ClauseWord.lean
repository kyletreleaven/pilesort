import PileSort.Reduction.SATToShuffle.VarEncodingLemmas
import PileSort.MatchingChain.Mono
import PileSort.Reduction.SATToMatchingChain.Defs.FormulaDefs
import PileSort.Reduction.SATToMatchingChain.Gadgets.StartClause
import PileSort.Reduction.SATToMatchingChain.TestConsume
import PileSort.Reduction.SATToMatchingChain.TestChain
import PileSort.Reduction.SATToMatchingChain.Gadgets.Next

/-!
  Correctness of `clauseWord`: the gadget that tests whether a clause is satisfied.

  A clause is satisfied if at least one of its literals matches the variable
  assignment.  `clauseWord` implements this as a sequence: START_CLAUSE
  initializes the non-activated state (NACTD), activation gadgets test each
  variable in turn (flipping NACTD → ACTD on the first match), and the final
  end-activation gadget resolves the outcome — END_POS if satisfied, chain
  penalty (≥ CHAIN_DISQ) if not.  NEXT then advances to the next clause block.

  ## Theorems

  `clauseWord_start_sat_cons` / `clauseWord_start_nonsat_cons` prove the
  single-clause outcome.  `clauseNext_good_consumption`,
  `clauseNext_bad_consumption`, and `clauseNext_chain_consumption` lift this
  to `clauseWord ++ NEXT` on a replicated-types machine, consuming one copy
  of `xs` per clause — the inductive engine for `FormulaWord.lean`.
-/

theorem list_drop_append_two {α : Type} (A1 A2 : List α) (k : Nat) (hA1 : A1.length = k + 2) :
    (A1 ++ A2).drop k = A1[k]'(by omega) :: A1[k + 1]'(by omega) :: A2 := by
  rw [List.drop_append_eq_append_drop, show k - A1.length = 0 from by omega,
      List.drop_zero, list_drop_two A1 k hA1]; simp

theorem list_drop_append_two_last {α : Type} (A1 A2 : List α) (n : Nat)
    (hA1 : A1.length = n + 1) (hn : n ≥ 1) :
    (A1 ++ A2).drop (n - 1) = A1[n - 1]'(by omega) :: A1[n]'(by omega) :: A2 := by
  rw [List.drop_append_eq_append_drop, show n - 1 - A1.length = 0 from by omega,
      List.drop_zero, list_drop_two A1 (n - 1) (by omega)]
  simp [show n - 1 + 1 = n from by omega]

/-- clauseWord in consumption form from CHAIN_DISQ: consumes n+1 blocks.

    Proof: unfold clauseWord, start_clause_disq + testChain_disq_cons + endTestWord_consumption_disq. -/
theorem clauseWord_chain_consumption (n : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hn : n ≥ 1)
    (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    applyWord (clauseWord n clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) CHAIN_DISQ ≥
    (n + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  unfold clauseWord
  rw [show START_CLAUSE ++ (List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (n - 1) clause ++ suffix =
      START_CLAUSE ++ ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        (endTestWord (n - 1) clause ++ suffix)) from by simp [List.append_assoc]]
  obtain ⟨t, rest, rfl⟩ : ∃ t rest, A1 = t :: rest := by
    match A1, hA1 with | a :: as, _ => exact ⟨a, as, rfl⟩
  simp only [List.cons_append]
  rw [List.range_eq_range']
  -- 1. start_clause_disq: CHAIN_DISQ → ≥ CLAUSE_DISQ on same machine
  have hsc := start_clause_disq
    ((List.range' 0 (n - 1)).flatMap (fun i => testWord i clause) ++ (endTestWord (n - 1) clause ++ suffix))
    t (rest ++ A2)
  -- 2. testChain_disq_cons: n-1 testWords, consuming (t :: rest).take (n-1)
  have hC_ne : (t :: rest).drop (n - 1) ++ A2 ≠ [] := by
    cases h : (t :: rest).drop (n - 1) with
    | nil =>
      exfalso; have := congrArg List.length h
      simp [List.length_drop, hA1] at this; omega
    | cons _ _ => simp
  have htc := testChain_disq_cons ((t :: rest).take (n - 1)) ((t :: rest).drop (n - 1) ++ A2)
    0 clause (endTestWord (n - 1) clause ++ suffix) hC_ne
  rw [show (t :: rest).take (n - 1) ++ ((t :: rest).drop (n - 1) ++ A2) = (t :: rest) ++ A2 from by
      rw [← List.append_assoc, List.take_append_drop]] at htc
  simp only [List.cons_append] at htc
  rw [show ((t :: rest).take (n - 1)).length = n - 1 from by
      rw [List.length_take]; simp [hA1]; omega] at htc
  -- 3. Rewrite (t :: rest).drop (n-1) ++ A2 to x :: y :: A2 form
  have hdrop : (t :: rest).drop (n - 1) ++ A2 =
      (t :: rest)[n - 1]'(by simp [hA1]; omega) :: (t :: rest)[n]'(by simp [hA1]) :: A2 := by
    have h : ((t :: rest) ++ A2).drop (n - 1) = (t :: rest).drop (n - 1) ++ A2 := by
      rw [List.drop_append_eq_append_drop,
          show n - 1 - (t :: rest).length = 0 from by simp [hA1]; omega, List.drop_zero]
    rw [← h]; exact list_drop_append_two_last (t :: rest) A2 n hA1 (by omega)
  rw [hdrop] at htc
  -- 4. endTestWord_consumption_disq
  have hend := endTestWord_consumption_disq (n - 1) clause suffix
    ((t :: rest)[n - 1]'(by simp [hA1]; omega)) ((t :: rest)[n]'(by simp [hA1])) A2 hA2
  -- 5. Combine
  show _ ≥ (n + 1) * ALIGN.length + _
  rw [show (n + 1) * ALIGN.length = (n - 1) * ALIGN.length + 2 * ALIGN.length from by
      rw [show n + 1 = (n - 1) + 2 from by omega, Nat.add_mul]]
  omega


/-- Adapter: converts `hasMatchingAssignment_some_matchesLiteral` output into the activation
    hypothesis form expected by `testChain_nactd_end_endpos` (with prefix A1.take (n-1),
    end element A1[n-1], and offset j = 0). -/
theorem hasMatchingAssignment_activation (n : Nat) (A1 : List PileType) (clause : Clause)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1)
    (h : HasMatchingAssignment n A1 (satisfiesClause · clause)) :
    (∃ i : Fin (A1.take (n - 1)).length, matchesLiteral (A1.take (n - 1))[i] (0 + ↑i) clause) ∨
      matchesLiteral (A1[n - 1]'(by omega)) (0 + (A1.take (n - 1)).length) clause := by
  obtain ⟨⟨i, hi⟩, hml⟩ := hasMatchingAssignment_some_matchesLiteral n A1 clause hA1 h
  -- hi : i < n,  hml : matchesLiteral (A1[i]'_) i clause
  have htake_len : (A1.take (n - 1)).length = n - 1 := by rw [List.length_take]; omega
  by_cases hlt : i < n - 1
  · refine Or.inl ⟨⟨i, by rw [htake_len]; exact hlt⟩, ?_⟩
    simp only [Nat.zero_add]
    have hval : (A1.take (n - 1))[i]'(by rw [List.length_take]; omega) = A1[i]'(by omega) := by
      apply List.getElem_take
    exact hval ▸ hml
  · have heq : i = n - 1 := by omega
    subst heq
    simp only [htake_len, Nat.zero_add]
    exact Or.inr hml

/-- clauseWord ++ suffix from START_POS reduces to testWords ++ endTestWord ++ suffix from NACTD. -/
theorem clauseWord_start_preamble_cons (n : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = n + 1) :
    applyWord (clauseWord n clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) START_POS =
    applyWord ((List.range' 0 (n - 1)).flatMap (fun i => testWord i clause) ++
      (endTestWord (n - 1) clause ++ suffix))
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD := by
  unfold clauseWord
  rw [show START_CLAUSE ++ (List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (n - 1) clause ++ suffix =
      START_CLAUSE ++ ((List.range' 0 (n - 1)).flatMap (fun i => testWord i clause) ++
        (endTestWord (n - 1) clause ++ suffix)) from by
    simp [List.range_eq_range', List.append_assoc]]
  obtain ⟨t, rest, rfl⟩ : ∃ t rest, A1 = t :: rest := by
    match A1, hA1 with | a :: as, _ => exact ⟨a, as, rfl⟩
  simp only [List.cons_append]
  rw [start_clause_start _ t (rest ++ A2)]

/-- clauseWord in consumption form from START_POS: nonsat case consumes n+1 blocks. -/
theorem clauseWord_start_nonsat_cons (n : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ [])
    (hno : ¬HasMatchingAssignment n A1 (satisfiesClause · clause)) :
    applyWord (clauseWord n clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) START_POS ≥
      (n + 1) * ALIGN.length +
        applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  rw [clauseWord_start_preamble_cons n clause suffix A1 A2 hA1]
  have hA2' : A1.drop (n - 1) ++ A2 ≠ [] := by
    cases h : A1.drop (n - 1) with
    | nil => exfalso; have := congrArg List.length h; simp [List.length_drop, hA1] at this; omega
    | cons _ _ => simp
  have hdrop : A1.drop (n - 1) ++ A2 =
      A1[n - 1]'(by omega) :: A1[n]'(by omega) :: A2 := by
    have h : (A1 ++ A2).drop (n - 1) = A1.drop (n - 1) ++ A2 := by
      rw [List.drop_append_eq_append_drop, show n - 1 - A1.length = 0 from by omega, List.drop_zero]
    rw [← h]; exact list_drop_append_two_last A1 A2 n hA1 (by omega)
  have htake_len : (A1.take (n - 1)).length = n - 1 := by rw [List.length_take]; omega
  show _ ≥ (n + 1) * ALIGN.length + _
  rw [show (n + 1) * ALIGN.length = (n - 1) * ALIGN.length + 2 * ALIGN.length from by
      rw [show n + 1 = (n - 1) + 2 from by omega, Nat.add_mul]]
  cases ht : A1[n]'(by omega) with
  | Q =>
    have hnoml := not_hasMatchingAssignment_no_matchesLiteral n A1 clause hA1 ht hno
    have htc := testChain_nactd_cons (A1.take (n - 1)) (A1.drop (n - 1) ++ A2)
      0 clause (endTestWord (n - 1) clause ++ suffix) hA2'
    rw [show A1.take (n - 1) ++ (A1.drop (n - 1) ++ A2) = A1 ++ A2 from by
        rw [← List.append_assoc, List.take_append_drop]] at htc
    -- Eliminate the if before rewriting the length (avoids dependent rewrite issue)
    have hex_neg : ¬∃ i : Fin (A1.take (n - 1)).length,
        matchesLiteral (A1.take (n - 1))[i] (0 + ↑i) clause := by
      rintro ⟨⟨i, hi⟩, hm⟩
      simp only [Nat.zero_add] at hm
      have hi' : i < A1.length := by rw [List.length_take] at hi; omega
      have hval : (A1.take (n - 1))[i]'hi = A1[i]'hi' := by apply List.getElem_take
      exact hnoml i (by omega) (hval ▸ hm)
    rw [if_neg hex_neg, htake_len] at htc
    rw [htc, hdrop, ht]
    have hend := endTestWord_consumption_nactd (n - 1) clause suffix
      (A1[n - 1]'(by omega)) PileType.Q A2 hA2
    rw [if_neg (fun ⟨_, h⟩ => hnoml (n - 1) (by omega) h)] at hend
    omega
  | S =>
    have hmono := applyWord_mono
      ((List.range' 0 (n - 1)).flatMap (fun i => testWord i clause) ++ (endTestWord (n - 1) clause ++ suffix))
      (virtualPileTypes ALIGN (A1 ++ A2)) (show ACTD ≤ NACTD from by decide)
    have htc := testChain_actd_cons (A1.take (n - 1)) (A1.drop (n - 1) ++ A2)
      0 clause (endTestWord (n - 1) clause ++ suffix) hA2'
    rw [show A1.take (n - 1) ++ (A1.drop (n - 1) ++ A2) = A1 ++ A2 from by
        rw [← List.append_assoc, List.take_append_drop], htake_len] at htc
    rw [hdrop, ht] at htc
    have hend := endTestWord_consumption_actd (n - 1) clause suffix
      (A1[n - 1]'(by omega)) PileType.S A2 hA2
    rw [if_neg (by decide)] at hend
    omega

/-- clauseWord in consumption form from START_POS: sat case.
    When the clause has a satisfying assignment, consumes n blocks and lands at END_POS. -/
theorem clauseWord_start_sat_cons (n : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ [])
    (h : HasMatchingAssignment n A1 (satisfiesClause · clause)) :
    applyWord (clauseWord n clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) START_POS =
    n * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  obtain ⟨vars, hvars, hA1eq, hsat⟩ := h
  have hQ : A1[n]'(by omega) = PileType.Q := by
    subst hA1eq
    rw [List.getElem_append_right (by simp [embedVars, List.length_map, hvars])]
    simp [embedVars, List.length_map, hvars]
  have hmachine : A1 ++ A2 =
      A1.take (n - 1) ++ A1[n - 1]'(by omega) :: PileType.Q :: A2 := by
    have hdrop : A1.drop (n - 1) ++ A2 = A1[n - 1]'(by omega) :: PileType.Q :: A2 := by
      have h : (A1 ++ A2).drop (n - 1) = A1.drop (n - 1) ++ A2 := by
        rw [List.drop_append_eq_append_drop,
            show n - 1 - A1.length = 0 from by omega, List.drop_zero]
      rw [← h, list_drop_append_two_last A1 A2 n hA1 (by omega), hQ]
    rw [← hdrop, ← List.append_assoc, List.take_append_drop]
  have hact' := hasMatchingAssignment_activation n A1 clause hn hA1 ⟨vars, hvars, hA1eq, hsat⟩
  rw [clauseWord_start_preamble_cons n clause suffix A1 A2 hA1, ← List.append_assoc, hmachine]
  have htake_len : (A1.take (n - 1)).length = n - 1 := by rw [List.length_take]; omega
  have hend := testChain_nactd_end_endpos 0 clause suffix
    (A1.take (n - 1)) (A1[n - 1]'(by omega)) A2 hA2 hact'
  simp only [Nat.zero_add, htake_len, show n - 1 + 1 = n from by omega] at hend
  exact hend

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
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten) :=
    virtualPileTypes_replicate_peel ALIGN xs m (by omega)
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have hxs_ne : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    match m, hm with
    | m' + 2, _ => simp [List.replicate_succ, List.flatten_cons, hxs_ne]
  rw [h_eq]
  have hcw : applyWord (clauseWord n c)
      (compile (virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten))) START_POS =
      END_POS + n * ALIGN.length := by
    have h := clauseWord_start_sat_cons n c [] xs _ hn hxs_len hA2 ⟨vars, hvars, hxs, hsat⟩
    have hnil : ∀ (f : Action → Nat → Nat) s, applyWord [] f s = s := fun _ _ => rfl
    simp only [List.append_nil, hnil] at h; omega
  rw [hcw]
  have hk : n < (xs ++ (List.replicate (m - 1) xs).flatten).length := by simp; omega
  rw [next_correct (xs ++ (List.replicate (m - 1) xs).flatten) n hk, hxs_len]
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
  rw [applyWord_append, applyWord_append]
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
  have h_cw_s : applyWord (clauseWord n c)
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)))
      s ≥ CHAIN_DISQ + xs.length * ALIGN.length :=
    Nat.le_trans h_cw (applyWord_mono (clauseWord n c) _ hs)
  have h_mono := applyWord_mono suffix
    (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q))
    (Nat.le_trans h_cw_s
      (applyWord_ge NEXT (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)) _))
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
