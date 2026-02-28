# Plan: Simplify ClauseWord.lean

## 1. Eliminate getD/getElem bridge lemmas (highest impact)

Restate `satisfiesClause_first_matchesLiteral` to produce `getElem` results directly,
taking `A1 : List PileType` with `A1 = embedVars vars ++ [Q]` as input.

**Eliminates:**
- `matchesLiteral_embedVars_getD` (lines 439-446)
- `matchesLiteral_getD_eq_getElem` (lines 488-493)
- The 8-line conversion block in `clauseWord_start_sat` (lines 517-524)

## 2. Restate `testChain_nactd` on `A1 ++ A2` directly

Change `testChain_nactd` to take `A1 ++ A2` with `hno` using `A1[i]` instead of
generic `types` with `types[i]`. Eliminates `testChain_nactd_split` adapter.

## 3. Merge `testChain_sat_end_lt` and `testChain_sat_end_eq` (speculative)

May not actually simplify due to different proof machinery. Investigate.

## 4. Inline `list_drop_append_two_last`

Only used once (line 611). Inline it and remove the lemma.

## 5. Simplify `satisfiesClause_first_matchesLiteral` proof

The 30-line induction is verbose. Consider alternatives, but may not save much without Mathlib.
