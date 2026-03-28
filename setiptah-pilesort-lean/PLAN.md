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

---

## Current critical path: binary common lemmas

`PileSort/MultiRoundFuture.lean` is now effectively the replacement for the old
`MultiRound.lean`, modulo the remaining shared binary/spec-level lemmas in
`PileSort/MultiRoundCommon.lean`.

The remaining `sorry`s there are:

- `shuffleRound_virtualPileTypes`
- `virtualPileTypes_assoc`
- `combinedSpec_assoc`
- `combinedSpec_splitSpec`

The main bottleneck is `shuffleRound_virtualPileTypes`; the others sit above or
beside that binary composition layer.

---

## `shuffleRound_virtualPileTypes`

Target theorem (now in `MultiRoundCommon.lean`):

```
shuffleRound (shuffleRound d pt1 assign1) pt2 assign2
  = shuffleRound d (virtualPileTypes pt1 pt2) (combinedAssign pt1 pt2 assign1 assign2)
```

### Current proof strategy

1. Reduce deck equality to order equality on cards.
   This is now packaged as `deck_eq_of_order_iff`.

2. View one-round shuffle order lexicographically.
   The paper’s viewpoint is that the output order of one round is determined by
   the lexicographic key

   ```
   (assign c, orient (types.get (assign c)) d.posOf c)
   ```

   where `orient Q x = x` and `orient S x = rev x`.

3. For two rounds, the resulting comparison key has three coordinates:

   ```
   ( assign2 c
   , orient (pt2.get (assign2 c)) assign1 c
   , composite orientation of d.posOf c from both pile-type phases )
   ```

   Intuitively:
   - first compare the outer pile
   - inside a fixed outer pile, compare the inner pile, oriented by the outer pile type
   - inside a fixed inner pile, compare the original deck position, oriented by
     the net effect of both pile types

4. Compress the first two coordinates by mixed radix.
   `combinedAssign` is exactly this compression:

   ```
   combinedAssign c =
     assign2 c * pt1.length +
     (orient (pt2.get (assign2 c)) assign1 c).val
   ```

   So the two-round lex key should match a one-round lex key for the virtual round.

5. Identify the virtual pile type at the compressed index.
   `virtualPileTypes_getElem` should show that the virtual pile type at the
   combined index is exactly the type needed to orient the third coordinate correctly.

### Likely helper lemmas

- one-round lex-order theorem phrased with `orient`
- block-order lemma for `combinedAssign`
- same-block comparison lemma reducing `combinedAssign` order to the oriented
  inner assignment order
- virtual-pile lookup lemma for the combined index

The goal is to keep the main theorem close to the paper’s lexicographic argument,
instead of proving it by one long nested case split from `shuffleRound_order`.

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
