/-
  Adapter lemmas lifting clauseWord_correct to the replicated-types form used
  by FormulaWord.lean.

  ## Design note: `hQ` hypothesis rejected

  An attempted simplification added `hQ : A1[n] = Q` to `clauseWord_start_nonsat`
  to eliminate the S case (~40 lines of case analysis). This was rejected because
  the penalty path (`formulaState_penalty_start` → `clauseWord_sat.2` /
  `clauseNext_sat.2`) is called with arbitrary `xs` where `xs[n]` can be S.
  Threading `hQ` through would have required restructuring `clauseWord_sat`,
  `clauseNext_sat`, `formulaState_penalty_start`, `formulaState_penalty_all`,
  `formulaWord_unsat_pos`, and a top-level case split in `formulaWord_correct'`
  — net complexity increase rather than decrease.
-/
import PileSort.ClauseWord

/-- Preamble: clauseWord from START_POS reduces to testWords ++ endTestWord from NACTD,
    after factoring out A0 and applying start_clause_start. -/
theorem clauseWord_start_preamble (n : Nat) (clause : Clause)
    (A1 A2 : List PileType)
    (hA1 : A1.length = n + 1) :
    applyWord (clauseWord n clause)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) START_POS =
    applyWord ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
      endTestWord (n - 1) clause)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD := by
  -- 1. Unfold clauseWord, reassociate as START_CLAUSE ++ rest
  unfold clauseWord
  rw [show START_CLAUSE ++ (List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (n - 1) clause =
      START_CLAUSE ++ ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (n - 1) clause) from by simp [List.append_assoc]]
  -- 2. A1 is nonempty; start_clause_start → NACTD
  obtain ⟨t, rest, rfl⟩ : ∃ t rest, A1 = t :: rest := by
    match A1, hA1 with | a :: as, _ => exact ⟨a, as, rfl⟩
  rw [List.cons_append, start_clause_start _ t (rest ++ A2)]


/-- When A1 ends in Q and has no matching satisfying assignment,
    no matchesLiteral fires at any index. -/
theorem not_hasMatchingAssignment_no_matchesLiteral
    (n : Nat) (A1 : List PileType) (clause : Clause)
    (hA1 : A1.length = n + 1) (hQ : A1[n]'(by omega) = PileType.Q)
    (hno : ¬HasMatchingAssignment n A1 (satisfiesClause · clause)) :
    ∀ i (hi : i < n), ¬matchesLiteral (A1[i]'(by omega)) i clause := by
  -- A1 = init ++ [Q], init = embedVars vars
  obtain ⟨init, last, hsplit, hilen⟩ := list_split_last A1 (by intro h; simp [h] at hA1)
  have hlast : last = PileType.Q := by
    have h1 : A1[n]'(by omega) = last := by
      simp only [hsplit]
      rw [List.getElem_append_right (by omega)]
      simp
    rw [← h1]; exact hQ
  have hinit_len : init.length = n := by omega
  obtain ⟨vars, hvlen, hvars⟩ := embedVars_surjective init
  -- ¬satisfiesClause
  have hnotsat : ¬satisfiesClause vars clause := by
    intro hsat
    exact hno ⟨vars, hvlen ▸ hinit_len, hlast ▸ hvars ▸ hsplit, hsat⟩
  -- Pointwise ¬matchesLiteral
  intro i hi hml
  apply hnotsat
  -- A1[i] = init[i] = embedVar vars[i]
  have hAi : A1[i]'(by omega) = init[i]'(by omega) := by
    simp only [hsplit]; rw [List.getElem_append_left (by omega)]
  rw [hAi] at hml
  simp only [← hvars, embedVars, List.getElem_map] at hml
  -- hml : matchesLiteral (embedVar vars[i]) i clause
  rw [satisfiesClause_iff_matchesLiteral]
  have hvi : i < vars.length := by rw [hvlen]; omega
  exact ⟨i, hvi, by
    have : vars.getD i false = vars[i]'hvi := by
      simp [List.getD, List.getElem?_eq_getElem hvi]
    rw [this]
    exact hml⟩

/-- When vars satisfies a clause, there is a first index where matchesLiteral fires.
    Returns the first matching index with proof it's minimal. -/
theorem satisfiesClause_first_matchesLiteral
    (vars : List Bool) (clause : Clause)
    (hsat : satisfiesClause vars clause) :
    ∃ i₀ : Fin vars.length,
      matchesLiteral (embedVar vars[i₀]) i₀ clause ∧
      ∀ j : Fin vars.length, j < i₀ →
        ¬matchesLiteral (embedVar vars[j]) j clause := by
  -- From satisfiesClause, get some matching index
  rw [satisfiesClause_iff_matchesLiteral] at hsat
  obtain ⟨i, hi, hml⟩ := hsat
  have hml' : matchesLiteral (embedVar vars[i]) i clause := by
    rwa [show vars.getD i false = vars[i] from by
      simp [List.getD, List.getElem?_eq_getElem hi]] at hml
  -- Find the minimum by strong induction on the index
  have : ∀ k (hk : k < vars.length),
      matchesLiteral (embedVar vars[k]) k clause →
      ∃ i₀ : Fin vars.length,
        matchesLiteral (embedVar vars[i₀]) i₀ clause ∧
        ∀ j : Fin vars.length, j < i₀ →
          ¬matchesLiteral (embedVar vars[j]) j clause := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk hmlk
      by_cases hex : ∃ j : Fin vars.length, j.val < k ∧
          matchesLiteral (embedVar vars[j]) j clause
      · obtain ⟨⟨j, hj⟩, hjk, hmlj⟩ := hex
        exact ih j hjk hj hmlj
      · exact ⟨⟨k, hk⟩, hmlk, fun j hj hc =>
          hex ⟨j, hj, hc⟩⟩
  exact this i hi hml'

/-- clauseWord from START_POS: if a satisfying assignment matches A1, reaches END_POS;
    otherwise reaches the penalty zone. -/
theorem clauseWord_start_sat (n : Nat) (clause : Clause)
    (A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    let types := virtualPileTypes ALIGN (A1 ++ A2)
    ∀ vars : List Bool, vars.length = n → A1 = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars clause →
      applyWord (clauseWord n clause) (compile types) START_POS = END_POS + n * ALIGN.length := by
  simp only []
  intro vars hvars hA1eq hsat
  -- 1. Preamble: reduce to NACTD on testWords ++ endTestWord
  rw [clauseWord_start_preamble n clause A1 A2 hA1]
  -- 2. Find first activation index
  obtain ⟨⟨i₀, hi₀v⟩, hml_ev, hno_ev⟩ :=
    satisfiesClause_first_matchesLiteral vars clause hsat
  -- 3. Substitute A1 = embedVars vars ++ [Q] everywhere
  subst hA1eq
  have hevlen : (embedVars vars).length = n := by simp [embedVars, hvars]
  have hi₀n : i₀ < n := by omega
  -- Convert embedVar vars[i] to (embedVars vars ++ [Q])[i]
  have embed_eq : ∀ i (hi : i < n),
      (embedVars vars ++ [PileType.Q])[i]'(by simp [hevlen]; omega) = embedVar vars[i] := by
    intro i hi
    rw [List.getElem_append_left (by simp [hevlen]; omega)]
    simp [embedVars]
  have hml : matchesLiteral
      ((embedVars vars ++ [PileType.Q])[i₀]'(by simp [hevlen]; omega)) i₀ clause := by
    rw [embed_eq i₀ hi₀n]; exact hml_ev
  have hno : ∀ i (hi : i < i₀),
      ¬matchesLiteral
        ((embedVars vars ++ [PileType.Q])[i]'(by simp [hevlen]; omega)) i clause := by
    intro i hi hc
    exact hno_ev ⟨i, by omega⟩ hi (by rwa [embed_eq i (by omega)] at hc)
  -- 4. Apply testChain_sat_end_zero
  have hQ : (embedVars vars ++ [PileType.Q])[(n - 1) + 1]'(by simp [hevlen]; omega) =
      PileType.Q := by
    simp [List.getElem_append, hevlen, show n - 1 + 1 = n from by omega]
  have htse := testChain_sat_end_zero (n - 1) i₀ clause
    (embedVars vars ++ [PileType.Q]) A2
    (by simp [hevlen]; omega) hA2 hQ (by omega) hml hno
  simp only [show applyWord [] _ END_POS = END_POS from rfl] at htse
  rw [htse, show n - 1 + 1 = n from by omega]; omega

/-- clauseWord from START_POS without satisfying assignment → penalty.

    Proof:
    1. Unfold clauseWord. start_clause_start → NACTD on A1 ++ A2,
       applying testWords(0..n-2) ++ endTestWord(n-1).
    2. Case split on A1[n] (last element):
       2a. A1[n] = Q: Every PileType is Q or S, so A1 = embedVars vars ++ [Q] for unique vars.
           ¬HasMatchingAssignment → ¬satisfiesClause vars clause.
           Via satisfiesClause_iff_matchesLiteral, no matchesLiteral fires at any index.
           testChain_nactd_end with k=n-1 → ≥ (n+1)*m + CHAIN_DISQ.
       2b. A1[n] = S (≠ Q): Monotonicity (NACTD=3 ≥ ACTD=2), so bound by ACTD path.
           testChain_actd for n-1 steps + endTestWord_consumption ACTD with y≠Q → ≥ nextBad.
           Total: (n-1)*m + 2*m + CHAIN_DISQ = (n+1)*m + CHAIN_DISQ. -/
theorem clauseWord_start_nonsat (n : Nat) (clause : Clause)
    (A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    let types := virtualPileTypes ALIGN (A1 ++ A2)
    ¬ HasMatchingAssignment n A1 (satisfiesClause · clause) →
      applyWord (clauseWord n clause) (compile types) START_POS ≥
        CHAIN_DISQ + (n + 1) * ALIGN.length := by
  simp only []
  intro hno
  rw [clauseWord_start_preamble n clause A1 A2 hA1]
  suffices h : applyWord ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
      endTestWord (n - 1) clause) (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD ≥
      (n + 1) * ALIGN.length + CHAIN_DISQ by omega
  -- Case split on last element of A1
  cases ht : A1[n]'(by omega) with
  | Q =>
    -- Case 2a: A1[n] = Q, so A1 = embedVars vars ++ [Q] for some vars.
    -- Steps 1-3: no matchesLiteral fires anywhere
    have hnoml := not_hasMatchingAssignment_no_matchesLiteral n A1 clause hA1 ht hno
    -- Step 4: testChain_nactd_end with k=n-1, j=0
    simp only [List.range_eq_range']
    have hQ' : A1[(n - 1) + 1]'(by omega) = PileType.Q := by
      simp only [show n - 1 + 1 = n from by omega]; exact ht
    have hte := testChain_nactd_end_old (n - 1) 0 clause [] A1 A2 (by omega) hA2 hQ'
      (by intro i hi; simp; exact hnoml i (by omega))
      (by simp; exact hnoml (n - 1) (by omega))
    simp only [show 0 + (n - 1) = n - 1 from by omega,
      List.append_nil,
      show applyWord ([] : List Action) (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ = CHAIN_DISQ from rfl] at hte
    show _ ≥ (n + 1) * ALIGN.length + CHAIN_DISQ
    rw [show n + 1 = (n - 1) + 2 from by omega]
    exact hte
  | S =>
    -- Case 2b: A1[n] = S (≠ Q).
    -- Goal: applyWord (testWords ++ endTestWord) machine NACTD ≥ (n+1)*m + CHAIN_DISQ
    -- Let W = testWords ++ endTestWord, M = machine.
    -- Step 1: applyWord_mono (ACTD ≤ NACTD): applyWord W M ACTD ≤ applyWord W M NACTD.
    -- Step 2: testChain_actd (n-1) 0 (suffix=endTestWord): applyWord W M ACTD
    --         = (n-1)*m + applyWord (endTestWord) M' ACTD
    --         where M' = vpt ALIGN (A1[n-1] :: A1[n] :: A2).
    -- Step 3: Substitute A1[n] = S in Step 2 result.
    -- Step 4: endTestWord_consumption ACTD with y=S≠Q, suffix=[]:
    --         applyWord (endTestWord) M' ACTD ≥ 2*m + CHAIN_DISQ.
    -- Step 5: Combine Steps 1-4:
    --         applyWord W M NACTD ≥ applyWord W M ACTD
    --           = (n-1)*m + applyWord (endTestWord) M' ACTD
    --           ≥ (n-1)*m + 2*m + CHAIN_DISQ = (n+1)*m + CHAIN_DISQ.
    -- Step 1: mono
    have hmono := applyWord_mono
      ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++ endTestWord (n - 1) clause)
      (virtualPileTypes ALIGN (A1 ++ A2))
      (show ACTD ≤ NACTD from by decide)
    -- Step 2: testChain_actd, using list_drop_append_two_last so indices use A1[n] not A1[n-1+1]
    simp only [List.range_eq_range'] at hmono ⊢
    have htc := testChain_actd (n - 1) 0 clause
      (endTestWord (n - 1) clause) (A1 ++ A2) (by simp [hA1]; omega)
    rw [list_drop_append_two_last A1 A2 n hA1 hn] at htc
    -- Steps 3-4: endTestWord_consumption ACTD with y = S ≠ Q
    have hend := endTestWord_consumption_actd (n - 1) clause []
      (A1[n - 1]'(by omega)) (A1[n]'(by omega)) A2 hA2
    simp only [ht, show PileType.S = PileType.Q ↔ False from by decide,
      false_iff, ite_false, List.append_nil,
      show applyWord ([] : List Action) (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ = CHAIN_DISQ from rfl] at hend
    -- Step 5: calc chain
    simp only [ht] at htc
    calc (n + 1) * ALIGN.length + CHAIN_DISQ
        = (n - 1) * ALIGN.length + 2 * ALIGN.length + CHAIN_DISQ := by
          rw [show n + 1 = (n - 1) + 2 from by omega, Nat.add_mul]
      _ ≤ (n - 1) * ALIGN.length +
            applyWord (endTestWord (n - 1) clause)
              (compile (virtualPileTypes ALIGN (A1[n - 1]'(by omega) :: PileType.S :: A2))) ACTD :=
          Nat.add_le_add_left hend _
      _ = applyWord _ _ ACTD := htc.symm
      _ ≤ applyWord _ _ NACTD := hmono

open Classical in
/-- Consumption form of clauseWord from START_POS with suffix:
    - Sat case:   result = applyWord suffix machine (END_POS + n*m)
                  (END_POS is inside A1's block so no further shift is possible)
    - Nonsat case: result ≥ (n+1)*m + applyWord suffix A2_machine CHAIN_DISQ
                  (clauseWord reaches ≥ CHAIN_DISQ + (n+1)*m, which is exactly the A1/A2 boundary) -/
theorem clauseWord_start_consumption (n : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    let machine := compile (virtualPileTypes ALIGN (A1 ++ A2))
    if HasMatchingAssignment n A1 (satisfiesClause · clause) then
      applyWord (clauseWord n clause ++ suffix) machine START_POS =
        applyWord suffix machine (END_POS + n * ALIGN.length)
    else
      applyWord (clauseWord n clause ++ suffix) machine START_POS ≥
        (n + 1) * ALIGN.length +
          applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  simp only []
  rcases Classical.em (HasMatchingAssignment n A1 (satisfiesClause · clause)) with h | h
  · rw [if_pos h]
    obtain ⟨vars, hvars, hA1eq, hsat⟩ := h
    rw [applyWord_append, clauseWord_start_sat n clause A1 A2 hn hA1 hA2 vars hvars hA1eq hsat]
  · rw [if_neg h]
    -- Nonsat case: clauseWord reaches ≥ CHAIN_DISQ + (n+1)*m, shift to A2 machine
    rw [applyWord_append]
    have hcw := clauseWord_start_nonsat n clause A1 A2 hn hA1 hA2 h
    have hshift : applyWord suffix (compile (virtualPileTypes ALIGN (A1 ++ A2)))
          (CHAIN_DISQ + (n + 1) * ALIGN.length) =
        (n + 1) * ALIGN.length +
          applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
      rw [virtualPileTypes_append,
          show CHAIN_DISQ + (n + 1) * ALIGN.length =
            (virtualPileTypes ALIGN A1).length + CHAIN_DISQ from by
            rw [virtualPileTypes_length, hA1]; omega,
          applyWord_compile_append_shift, virtualPileTypes_length, hA1]
    rw [← hshift]
    exact applyWord_mono suffix _ hcw

/-- Chaining testWords from CLAUSE_DISQ: each step shifts by one block and preserves ≥ CLAUSE_DISQ.
    After k steps on range' start k, the result is ≥ k * m + (suffix result on dropped types).

    Induction on k:
    - k = 0: range' is empty, trivial.
    - k + 1: peel off testWord start via range'_succ + flatMap_cons.
      testWord_consumption (CLAUSE_DISQ case) gives ≥ m + (rest on tail).
      IH gives rest on tail ≥ k * m + (suffix on drop). Combine with omega. -/
theorem testChain_disq : ∀ (k : Nat) (start : Nat) (clause : Clause)
    (suffix : List Action) (types : List PileType), k < types.length →
    applyWord ((List.range' start k).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN types)) CLAUSE_DISQ >=
    k * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (types.drop k))) CLAUSE_DISQ
  | 0, _, _, _, _, _ => by simp
  | k + 1, start, clause, suffix, [], htypes => by simp at htypes
  | k + 1, start, clause, suffix, x :: rest, htypes => by
    simp only [List.length_cons] at htypes
    have hrest : rest ≠ [] := by intro h; subst h; simp at htypes
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have htw := testWord_consumption_disq start clause
      ((List.range' (start + 1) k).flatMap (fun i => testWord i clause) ++ suffix)
      x rest hrest
    have hih := testChain_disq k (start + 1) clause suffix rest (by omega)
    show _ >= (k + 1) * ALIGN.length + applyWord suffix
      (compile (virtualPileTypes ALIGN (List.drop k rest))) CLAUSE_DISQ
    rw [Nat.succ_mul]; omega

/-- From CLAUSE_DISQ: k testWords (indices j..j+k-1) + endTestWord (j+k) reach
    penalty zone, consuming k+2 blocks total.

    Proof:
    1. Reassociate word as testWords ++ (endTestWord ++ suffix).
    2. testChain_disq (k steps): shifts by k*m, stays ≥ CLAUSE_DISQ on A1.drop(k) ++ A2.
    3. A1.drop(k) has ≥ 2 elements (since A1.length = k+2).
    4. endTestWord_consumption CLAUSE_DISQ case: ≥ 2*m + suffix from CHAIN_DISQ on A2.
    5. Total: k*m + 2*m = (k+2)*m. -/
theorem testChain_disq_end' (k j : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = k + 2) (hA2 : A2 ≠ []) :
    applyWord ((List.range' j k).flatMap (fun i => testWord i clause) ++
              endTestWord (j + k) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) CLAUSE_DISQ ≥
    (k + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  -- 1. Reassociate word, apply testChain_disq, rewrite drop
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from List.append_assoc ..]
  have htc := testChain_disq k j clause (endTestWord (j + k) clause ++ suffix) (A1 ++ A2) (by simp [hA1]; omega)
  rw [list_drop_append_two A1 A2 k hA1] at htc
  -- 2. endTestWord_consumption_disq
  have hend := endTestWord_consumption_disq (j + k) clause suffix (A1[k]'(by omega)) (A1[k + 1]'(by omega)) A2 hA2
  -- 3. Combine: htc ≥ k*m + hend, hend ≥ 2*m + suffix result
  show _ ≥ (k + 2) * ALIGN.length + _
  rw [show (k + 2) * ALIGN.length = k * ALIGN.length + 2 * ALIGN.length from by
    rw [Nat.add_mul]]; omega

/-- testWords ++ endTestWord from CLAUSE_DISQ: specialization of testChain_disq_end'
    with k = n-1, j = 0. -/
theorem testChain_disq_end (n : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hn : n ≥ 1)
    (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    applyWord ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
              endTestWord (n - 1) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) CLAUSE_DISQ ≥
    (n + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  rw [show List.range (n - 1) = List.range' 0 (n - 1) from List.range_eq_range' ..,
      show (n + 1) = (n - 1 + 2) from by omega,
      show endTestWord (n - 1) = endTestWord (0 + (n - 1)) from by simp]
  exact testChain_disq_end' (n - 1) 0 clause suffix A1 A2 (by omega) hA2
