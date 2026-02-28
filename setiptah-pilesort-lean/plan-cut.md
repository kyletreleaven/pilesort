# Plan: Simplify ClauseWord.lean

## 1. Eliminate getD/getElem bridge lemmas — DONE

Restated `satisfiesClause_first_matchesLiteral` to use `Fin vars.length` and
`embedVar vars[i₀]` directly. Dropped `n`/`hvars` params; used `Nat.strongRecOn`.

**Eliminated:**
- `matchesLiteral_embedVars_getD`
- `matchesLiteral_getD_eq_getElem`
- `List.getD_eq_getElem`

Net: -17 lines (851 → 834).

## 2. Restate `testChain_nactd` on `A1 ++ A2` directly

`testChain_nactd` takes generic `types` with `hno` using `types[i]`.
Every external call site passes `A1 ++ A2` and converts via `getElem_append_left`.

If restated on `A1 ++ A2` with `hno` on `A1[i]`:
- Eliminates `testChain_nactd_split` adapter (lines 182-193, used 2x)
- Simplifies `testChain_nactd_end` (line 234, currently does getElem_append_left inline)

Note: the recursive call (line 171) uses `x :: rest` not `A1 ++ A2`, so the
induction still needs the generic form internally. May need to keep generic version
as the inductive core and have the `A1 ++ A2` version as a corollary — which is
basically what `_split` already is. **Might not be worth it.**

## 3. Inline `list_drop_append_two_last` — easy win

Only used once (line 595 in `clauseWord_start_nonsat`). Inline it and delete the lemma.

## 4. Inline `testChain_activate_end_split` — easy win

Only used once (line 285 in `testChain_sat_end_lt`). It's a thin wrapper around
`testChain_activate_end` that converts `getElem_drop`. Could inline the conversion.

## 5. Merge `testChain_sat_end_lt` and `testChain_sat_end_eq` — speculative

Different proof machinery (`_lt` uses nactd_split + activate_end_split;
`_eq` uses nactd_split + endTestWord_consumption). May not simplify.

## 6. (Closed) Simplify `satisfiesClause_first_matchesLiteral` proof — DONE in #1

Replaced verbose bound-based induction with `Nat.strongRecOn` (20 lines vs 30).
