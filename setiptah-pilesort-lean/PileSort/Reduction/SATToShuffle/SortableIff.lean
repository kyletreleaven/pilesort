import PileSort.Reduction.ShuffleMultiRoundToSingle.MultiRound

/-!
  # Main reduction: SAT ↔ pile-sort sortability

  This file contains the top-level theorems connecting SAT satisfiability to
  pile-sort feasibility.

  ## The encoding

  Given a CNF formula with `n` variables and `m` clauses:

  - `formulaWord n clauses` is a sequence of ascent (`a`) and descent (`d`) actions
    encoding the formula structure.
  - `deckOfWord (formulaWord n clauses)` is a deck that encodes the formula as a
    permutation, via its consecutive ascent/descent pattern.
  - A candidate variable assignment `vars : List Bool` (length `n`) is encoded as
    a list of pile types `xs = embedVars vars ++ [Q]`.  In this context, Q encodes
    `true` and S encodes `false`; this is specific to variable assignments and does
    not extend to pile types generally.

  ## The theorem

  For a fixed `xs`, the formula-encoding deck is sortable in three rounds
  `[ALIGN, xs, List.replicate m Q]` if and only if the assignment encoded by `xs`
  satisfies the formula.

  Note: `xs` values not ending with `Q` do not correspond to any variable
  assignment.  Both sides of the equivalence uniformly reject such `xs`:
  `HasMatchingAssignment` is vacuously false, and the deck is not sortable.

  ## Note on NP-hardness

  This theorem is parametric in `xs`: it does not by itself show NP-hardness.
  NP-hardness follows from two observations:
  - `xs` values not ending in Q are uniformly rejected by both sides (as noted above).
  - `embedVars` gives a bijection between Boolean assignments of length `n` and
    `xs` values ending in Q.

  Together these mean: asking whether *any* `xs` makes the deck sortable is exactly
  asking whether the formula is satisfiable.

  ## Two forms

  `formulaWord_correct_sortable` states this as single-round sortability on the
  flattened virtual pile types; `formulaWord_correct_multiSortable` states it
  directly as three-round sortability, which is the more natural form.
-/

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
