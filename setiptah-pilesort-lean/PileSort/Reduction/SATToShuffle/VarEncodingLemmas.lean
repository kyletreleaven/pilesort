import PileSort.Reduction.SATToShuffle.VarEncoding
import PileSort.Lists

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
