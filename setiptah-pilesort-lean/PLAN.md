# Plan

## Completed

- `sortable_iff_accepts` ✅ — `Sortable d types ↔ accepts types (Deck.changeProfile d)`
- `formulaWord_correct` ✅ — consumption-form proof stack complete
  (TestChain → ClauseWordNew → FormulaWordNew → FormulaWord)
- `deckOfWord_changeProfile` ✅ — `Deck.changeProfile (deckOfWord word) = word`
  (used by the formula-word correctness stack)
- `formulaWord_correct_sortable` ✅
- `PileSort/MultiRoundFuture.lean` theorem stack ✅
  - spec-centered refactor complete
  - `multiShuffleRound_eq_shuffleRound` proved
  - `multiSortable_iff_sortable` proved
  - formula-word lemmas ported to the future-oriented file
- Heterogeneous pile facings formalized ✅ — `ShuffleSpec.types : List PileType`
  assigns an independent Q/S facing per pile; `formulaWord_correct_multiSortable`
  relates sort feasibility in this model to SAT satisfiability.
- `PileSort/MultiRoundCommon.lean` fully sorry-free ✅
  - `shuffleRound_virtualPileTypes` proved
  - `virtualPileTypes_assoc` proved (via `applyPile_virtualPileTypes` in `VirtualPileTypes.lean`)
  - `combinedSpec_splitSpec` proved

---

## Current state

The core proof is complete end-to-end.  `MultiRoundFuture.lean` is the canonical
multi-round module (`PileSort.lean` imports it directly); `MultiRound.lean` has
been deleted.

### Remaining cleanup

`ClauseWord.lean` still contains two dead-code theorems:
`testChain_actd` and `testChain_nactd_old`. Once deleted the file body is empty
and the file itself can be removed (update imports in `FormulaWord.lean` and
`PileSort.lean` accordingly).

## Representation mismatch (open)

The `HasMatchingAssignment` / `embedVars` / `satisfiesClause` layer and the
`matchesLiteral` layer on raw pile types speak different languages.  Bridging
is currently done ad hoc:

- **Positive direction**: `hasMatchingAssignment_some_matchesLiteral` +
  `hasMatchingAssignment_activation` (adapter) in `ClauseWordNew.lean`.
- **Negative direction**: `not_hasMatchingAssignment_no_matchesLiteral` in
  `FormulaWordNew.lean`.

The open question is whether to push the `satisfiesClause`/`HasMatchingAssignment`
vocabulary *down* into the TestChain lemmas (so `testChain_nactd_end_endpos` and
friends accept `HasMatchingAssignment` hypotheses directly), or to keep the bridge
lemmas as a thin adapter layer above TestChain.  The current adapter approach works
and keeps TestChain free of SAT vocabulary; the alternative would shorten the
clauseWord proofs at the cost of coupling TestChain to the reduction layer.

## Index-based vs. destructured forms (open)

The TestChain.lean docstring discusses the two parameterization styles.  The
current lemmas all use the destructured (`A1 ++ A2`) form.  It is worth
investigating empirically whether any call sites would be materially simpler with
the index form, or whether the destructured form is uniformly preferable.  The
conversion between forms is cheap (a length lemma plus `List.take_append_drop`),
so the choice can be revisited per-lemma without cascading changes.

## Naming conventions (open)

Theorem and definition names across the project are inconsistent and do not
always make the content of a lemma obvious from its name.  A naming-convention
pass is planned to make the proof stack easier to navigate.  This is best done
after the representation-mismatch question is settled (since that may rename or
reorganize some of the bridge lemmas).

