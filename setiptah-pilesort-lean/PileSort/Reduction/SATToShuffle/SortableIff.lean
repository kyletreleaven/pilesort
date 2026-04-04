import PileSort.Reduction.ShuffleMultiRoundToSingle.MultiRound

/-- Main reduction theorem: the deck realizing a formula word is sortable by the
    pile-sort machine iff the formula is satisfiable. -/
theorem formulaWord_correct_sortable (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hne : clauses ≠ []) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate clauses.length PileType.Q)
    Sortable (deckOfWord (formulaWord n clauses)) types ↔
      HasMatchingAssignment n xs (satisfiesFormula · clauses) := by
  intro types
  rw [sortable_iff_accepts (Nat.succ_pos _), deckOfWord_changeProfile]
  exact formulaWord_correct n clauses xs hn hxs_len hne

/-- Main reduction theorem (multi-round form): the deck realizing a formula word is
    sortable in three rounds (ALIGN, xs, replicate Q) iff the formula is satisfiable. -/
theorem formulaWord_correct_multiSortable (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hne : clauses ≠ []) :
    MultiSortable (deckOfWord (formulaWord n clauses))
      [ALIGN, xs, List.replicate clauses.length PileType.Q] ↔
      HasMatchingAssignment n xs (satisfiesFormula · clauses) := by
  rw [multiSortable_iff_sortable]
  have hbase : virtualPileTypes (List.replicate clauses.length PileType.Q) [PileType.Q] =
      List.replicate clauses.length PileType.Q := by
    simp [virtualPileTypes, applyPile]
  change Sortable (deckOfWord (formulaWord n clauses))
    (foldVirtualPileTypesFuture [ALIGN, xs, List.replicate clauses.length PileType.Q]) ↔ _
  simp [foldVirtualPileTypesFuture, hbase]
  rw [(virtualPileTypes_assoc ALIGN xs (List.replicate clauses.length PileType.Q)).symm]
  exact formulaWord_correct_sortable n clauses xs hn hxs_len hne
