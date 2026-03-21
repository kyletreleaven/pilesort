# Plan

## Completed

- `sortable_iff_accepts` ✅ — `Sortable d types ↔ accepts types (Deck.changeProfile d)`
- `formulaWord_correct` ✅ — consumption-form proof stack complete
  (TestChain → ClauseWordNew → FormulaWordNew → FormulaWord)
- `deckOfWord_changeProfile` ✅ — `Deck.changeProfile (deckOfWord word) = word`
  (MultiRound.lean; enables formulaWord_correct_sortable)

---

## Next goal: `formulaWord_correct_sortable`

Compose the three completed results:

```
sortable_iff_accepts + deckOfWord_changeProfile + formulaWord_correct
  ⟹  formulaWord_correct_sortable
```

Concretely: given `word` and pile types `types`, the deck `deckOfWord word` is
sortable by `types` iff the formula word accepts (or equivalent SAT condition).

---

## Multi-round reduces to single-round on virtual piles

Target theorem (in MultiRound.lean):

```
shuffleRound (shuffleRound d pt1 assign1) pt2 assign2
  = shuffleRound d (virtualPileTypes pt1 pt2) combinedAssign
```

This says two successive pile-shuffle rounds are equivalent to one round on
`virtualPileTypes pt1 pt2`, with a combined assignment that encodes both rounds.

### Proof roadmap

1. **`shuffleRound_order`** ✅ — the output ordering of `shuffleRound d types assign`
   is determined solely by the pile assignment and pile types.

2. **`combinedAssign`** ✅ — defined:
   `combinedAssign c = assign2 c * pt1.length + f(assign2 c, assign1 c)`
   where `f` adjusts based on whether `pt2[assign2 c]` is Q (identity) or S (reversed).

3. **`virtualPileTypes_getElem`** — the virtual pile type at index
   `j * pt1.length + i` matches the composed condition from both rounds.

4. **`shuffleRound_virtualPileTypes`** (sorry) — main equality by `Deck.ext`.

---

## Remaining cleanup

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

## Heterogeneous pile facings (future)

A longer-term goal is to develop a mathematical model of pile shuffle that allows
*heterogeneous pile facings*: all cards within a single pile face the same direction
(up or down), but different piles in the same round may have different facings.
The goal is to relate sort feasibility in that model to the main NP-hardness reduction.
This is independent of the current Lean formalization work and can proceed in
parallel once the reduction proof is polished.
