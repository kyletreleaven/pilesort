# Plan

## Current state

The core proof is complete end-to-end.  The top-level theorem is
`formulaWord_correct_multiSortable` in `Reduction/SATToShuffle/SortableIff.lean`.

### Remaining cleanup

`ClauseWord.lean` holds the index-form counterparts of the destructured TestChain
lemmas (`testChain_actd`, `testChain_nactd_old`) and is retained while the
index-vs-destructured question below is open.  Once that question is resolved,
the file and its import in `PileSort.lean` can be removed.

---

## Open questions

### Representation mismatch

The `HasMatchingAssignment` / `embedVars` / `satisfiesClause` layer and the
`matchesLiteral` layer on raw pile types speak different languages.  Bridging
is currently done via adapter lemmas above the TestChain layer.  The open
question is whether to push the `satisfiesClause`/`HasMatchingAssignment`
vocabulary *down* into the TestChain lemmas, or keep the bridge as a thin
adapter.  The current approach keeps TestChain free of SAT vocabulary; the
alternative would shorten the clauseWord proofs at the cost of coupling.

### Index-based vs. destructured forms

The TestChain lemmas all use the destructured (`A1 ++ A2`) form.  It is worth
checking empirically whether any call sites would be simpler with the index
form.  The conversion is cheap (a length lemma plus `List.take_append_drop`),
so the choice can be revisited per-lemma without cascading changes.

### Naming conventions

Theorem and definition names across the project are inconsistent.  A
naming-convention pass is planned, best done after the representation-mismatch
question is settled.
