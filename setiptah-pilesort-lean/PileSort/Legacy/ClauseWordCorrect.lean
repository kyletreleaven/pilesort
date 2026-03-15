import PileSort.Legacy.ClauseWord

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

/-- clauseWord from CHAIN_DISQ: penalty propagates unconditionally.

    English proof:
    Apply clauseWord_chain_consumption (with empty suffix) on A1 ++ A2:
    result ≥ (n+1)*m + CHAIN_DISQ. ∎ -/
theorem clauseWord_chain (n : Nat) (clause : Clause)
    (A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    applyWord (clauseWord n clause) (compile (virtualPileTypes ALIGN (A1 ++ A2))) CHAIN_DISQ ≥
      CHAIN_DISQ + (n + 1) * ALIGN.length := by
  have hcc := clauseWord_chain_consumption n clause [] A1 A2 hn hA1 hA2
  simp only [List.append_nil,
    show applyWord ([] : List Action) (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ = CHAIN_DISQ
      from rfl] at hcc
  omega

/-- Combined clauseWord correctness, assembling start and chain parts. -/
theorem clauseWord_correct (n : Nat) (clause : Clause)
    (A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    let types := virtualPileTypes ALIGN (A1 ++ A2)
    (∀ vars : List Bool, vars.length = n → A1 = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars clause →
      applyWord (clauseWord n clause) (compile types) START_POS = END_POS + n * ALIGN.length)
    ∧
    (¬ HasMatchingAssignment n A1 (satisfiesClause · clause) →
      applyWord (clauseWord n clause) (compile types) START_POS ≥
        CHAIN_DISQ + (n + 1) * ALIGN.length)
    ∧
    applyWord (clauseWord n clause) (compile types) CHAIN_DISQ ≥
      CHAIN_DISQ + (n + 1) * ALIGN.length :=
  ⟨clauseWord_start_sat n clause A1 A2 hn hA1 hA2,
   clauseWord_start_nonsat n clause A1 A2 hn hA1 hA2,
   clauseWord_chain n clause A1 A2 hn hA1 hA2⟩

/-- clauseWord from START_POS on replicated types: if a matching assignment satisfies the
    clause, reaches END_POS + n * ALIGN.length; otherwise reaches ≥ CHAIN_DISQ + block.
    Repackages clauseWord_correct parts 1 and 2 for the List.replicate m .Q form. -/
theorem clauseWord_sat (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)
    (∀ vars : List Bool, vars.length = n → xs = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars c →
      applyWord (clauseWord n c) (compile types) START_POS =
        END_POS + n * ALIGN.length)
    ∧
    (¬ HasMatchingAssignment n xs (satisfiesClause · c) →
      CHAIN_DISQ + xs.length * ALIGN.length ≤
        applyWord (clauseWord n c) (compile types) START_POS) := by
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    have : m = (m - 1) + 1 := by omega
    rw [this, List.replicate_succ, List.flatten_cons]; simp
  rw [h_eq]
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    rw [show m - 1 = (m - 2) + 1 from by omega, List.replicate_succ, List.flatten_cons]
    simp [this]
  have hcw := clauseWord_correct n c xs ((List.replicate (m - 1) xs).flatten) hn hxs_len hA2
  constructor
  · exact hcw.1
  · intro hno
    calc CHAIN_DISQ + xs.length * ALIGN.length
        = CHAIN_DISQ + (n + 1) * ALIGN.length := by rw [hxs_len]
      _ ≤ _ := hcw.2.1 hno

/-- clauseWord from ≥ CHAIN_DISQ on replicated types always reaches ≥ CHAIN_DISQ + block.
    Repackages clauseWord_correct part 3 for the List.replicate m .Q form. -/
theorem clauseWord_penalty (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat) (s : Nat)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) (hs : CHAIN_DISQ ≤ s) :
    CHAIN_DISQ + xs.length * ALIGN.length ≤
      applyWord (clauseWord n c)
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q))) s := by
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    have : m = (m - 1) + 1 := by omega
    rw [this, List.replicate_succ, List.flatten_cons]; simp
  rw [h_eq]
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    rw [show m - 1 = (m - 2) + 1 from by omega, List.replicate_succ, List.flatten_cons]
    simp [this]
  have hcw := (clauseWord_correct n c xs ((List.replicate (m - 1) xs).flatten) hn hxs_len hA2).2.2
  calc CHAIN_DISQ + xs.length * ALIGN.length
      = CHAIN_DISQ + (n + 1) * ALIGN.length := by rw [hxs_len]
    _ ≤ applyWord (clauseWord n c) _ CHAIN_DISQ := hcw
    _ ≤ applyWord (clauseWord n c) _ s := applyWord_mono (clauseWord n c) _ hs
