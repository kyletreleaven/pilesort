# Plan

## Status

The consumption-form proof stack for `formulaWord_correct` is complete:

- **TestChain.lean** — plain-chain and end-capped consumption lemmas for
  `testWord` sequences.  Design notes and lemma inventory in the module docstring.
- **ClauseWordNew.lean** — `clauseWord_start_sat_cons`, `clauseWord_start_nonsat_cons`,
  `clauseWord_chain_consumption`, plus the representation-mismatch bridge lemmas
  `hasMatchingAssignment_some_matchesLiteral` and `hasMatchingAssignment_activation`.
- **FormulaWordNew.lean** — `clauseNext_good_consumption`, `clauseNext_bad_consumption`,
  `clauseNext_chain_consumption`.
- **FormulaWord.lean** — `formulaWord_correct` proved via the consumption stack.

Old proof machinery has been moved to `Legacy/` or deleted.

## Remaining cleanup

`ClauseWord.lean` still contains two index-form theorems that are dead code:
`testChain_actd` and `testChain_nactd_old`.  Once deleted the file body is empty
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
