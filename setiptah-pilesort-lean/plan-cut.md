# Plan: Simplify ClauseWord.lean

## 1. Eliminate getD/getElem bridge lemmas — DONE

Restated `satisfiesClause_first_matchesLiteral` to use `Fin vars.length` and
`embedVar vars[i₀]` directly. Dropped `n`/`hvars` params; used `Nat.strongRecOn`.

**Eliminated:**
- `matchesLiteral_embedVars_getD`
- `matchesLiteral_getD_eq_getElem`
- `List.getD_eq_getElem`

Net: -17 lines (851 → 834).

## 2. Restate `testChain_nactd` in consumption form — DONE

New `testChain_nactd` takes `A1 ++ A2` with induction on `A1`. Old version
renamed `testChain_nactd_old`.

## 3. Sentinel decomposition — IN PROGRESS

### Done
- `testChain_actd_cons` — consumption form of `testChain_actd` (new)
- `testChain_actd_end_new` — sentinel form (new)
- `testChain_nactd_end` — sentinel form (old renamed `_old`)
- `testChain_sat_end_eq` — sentinel form (old renamed `_old`)
- `testChain_activate_end_new` — 6-segment sentinel form (new)
- `testChain_sat_end_lt_new` — signature with `sorry`

### Parked
- `testChain_sat_end_lt_new` proof — ran into `cons_append`/`append_assoc`
  issues when composing multiple layers. May revisit after downstream
  lemmas are also restructured.

## 4. Propagate to `clauseWord_start_nonsat` — NEXT

Drop A0 param. Take `A1 ++ Q :: A2` structurally. The S case (~40 lines)
vanishes because no caller passes A1 ending in S.

Calls `not_hasMatchingAssignment_no_matchesLiteral` then
`testChain_nactd_end` (sentinel form, already done).

## 5. Propagate to `clauseWord_start_sat`

Similarly, take `embedVars vars` and Q structurally.

## 6. Cleanup

Delete all `_old` versions, `testChain_nactd_split`, `testChain_activate_end_split`,
and any list helper lemmas that become unused.
