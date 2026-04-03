import PileSort.Reduction.SATToMatchingChain.VarEncoding
import PileSort.Mono
import PileSort.Reduction
import PileSort.Reduction.SATToMatchingChain.Gadgets.StartClause
import PileSort.Reduction.SATToMatchingChain.TestConsume
import PileSort.TestChain

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

theorem list_split_last {α : Type} : ∀ (l : List α), l ≠ [] →
    ∃ init last, l = init ++ [last] ∧ init.length + 1 = l.length
  | [x], _ => ⟨[], x, rfl, rfl⟩
  | x :: y :: rest, _ => by
    have ⟨init, last, h, hlen⟩ := list_split_last (y :: rest) (by simp)
    exact ⟨x :: init, last, by rw [h]; simp, by simp_all [List.length_cons]⟩

/-- There exists a Boolean assignment of length n whose embedding matches xs
    and that satisfies predicate P (typically satisfiesClause or satisfiesFormula). -/
def HasMatchingAssignment (n : Nat) (xs : List PileType) (P : List Bool → Prop) : Prop :=
  ∃ vars : List Bool, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q] ∧ P vars

/-- matchesLiteral on an embedded Bool reduces to the literal satisfaction condition. -/
theorem matchesLiteral_embedVar (b : Bool) (i : Nat) (clause : Clause) :
    matchesLiteral (embedVar b) i clause ↔
      (clause.getD i .absent = .pos ∧ b = true) ∨ (clause.getD i .absent = .neg ∧ b = false) := by
  cases b <;> simp [matchesLiteral, litMatches, embedVar]

/-- satisfiesClause is equivalent to matchesLiteral firing at some in-range variable index. -/
theorem satisfiesClause_iff_matchesLiteral (vars : List Bool) (clause : Clause) :
    satisfiesClause vars clause ↔
      ∃ i, i < vars.length ∧ matchesLiteral (embedVar (vars.getD i false)) i clause := by
  simp only [satisfiesClause]
  exact exists_congr fun i => and_congr_right' (matchesLiteral_embedVar _ i clause).symm

/-- When A1 ends in Q and has no matching satisfying assignment,
    no matchesLiteral fires at any index. -/
theorem not_hasMatchingAssignment_no_matchesLiteral
    (n : Nat) (A1 : List PileType) (clause : Clause)
    (hA1 : A1.length = n + 1) (hQ : A1[n]'(by omega) = PileType.Q)
    (hno : ¬HasMatchingAssignment n A1 (satisfiesClause · clause)) :
    ∀ i (hi : i < n), ¬matchesLiteral (A1[i]'(by omega)) i clause := by
  obtain ⟨init, last, hsplit, hilen⟩ := list_split_last A1 (by intro h; simp [h] at hA1)
  have hlast : last = PileType.Q := by
    have h1 : A1[n]'(by omega) = last := by
      simp only [hsplit]; rw [List.getElem_append_right (by omega)]; simp
    rw [← h1]; exact hQ
  have hinit_len : init.length = n := by omega
  obtain ⟨vars, hvlen, hvars⟩ := embedVars_surjective init
  have hnotsat : ¬satisfiesClause vars clause := by
    intro hsat
    exact hno ⟨vars, hvlen ▸ hinit_len, hlast ▸ hvars ▸ hsplit, hsat⟩
  intro i hi hml
  apply hnotsat
  have hAi : A1[i]'(by omega) = init[i]'(by omega) := by
    simp only [hsplit]; rw [List.getElem_append_left (by omega)]
  rw [hAi] at hml
  simp only [← hvars, embedVars, List.getElem_map] at hml
  rw [satisfiesClause_iff_matchesLiteral]
  have hvi : i < vars.length := by rw [hvlen]; omega
  exact ⟨i, hvi, by
    have : vars.getD i false = vars[i]'hvi := by
      simp [List.getD, List.getElem?_eq_getElem hvi]
    rw [this]; exact hml⟩

/-- Positive companion to `not_hasMatchingAssignment_no_matchesLiteral`: when A1 has a
    satisfying assignment, some matchesLiteral fires at some index in [0, n). -/
theorem hasMatchingAssignment_some_matchesLiteral
    (n : Nat) (A1 : List PileType) (clause : Clause)
    (hA1 : A1.length = n + 1)
    (h : HasMatchingAssignment n A1 (satisfiesClause · clause)) :
    ∃ i : Fin n, matchesLiteral (A1[↑i]'(by omega)) ↑i clause := by
  obtain ⟨vars, hvars, hA1eq, hsat⟩ := h
  rw [satisfiesClause_iff_matchesLiteral] at hsat
  obtain ⟨i, hi, hml⟩ := hsat
  rw [hvars] at hi
  have hAi : A1[i]'(by omega) = embedVar (vars[i]'(by rw [hvars]; exact hi)) := by
    subst hA1eq; simp only [embedVars]
    rw [List.getElem_append_left (by rw [List.length_map, hvars]; exact hi), List.getElem_map]
  have hml' : matchesLiteral (A1[i]'(by omega)) i clause := by
    rw [hAi]
    have : vars.getD i false = vars[i]'(by rw [hvars]; exact hi) := by
      simp [List.getD, List.getElem?_eq_getElem (by rw [hvars]; exact hi)]
    rw [this] at hml; exact hml
  exact ⟨⟨i, by omega⟩, hml'⟩

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
