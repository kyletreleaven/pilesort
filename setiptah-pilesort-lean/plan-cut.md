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

## 4. Direction check — PAUSED

Considered two approaches for simplifying the remaining proofs:

**Decompositional (top-down):** Make Q structural in signatures, pass
list components as separate parameters. Eliminates the S case and
some index boilerplate, but creates `cons_append`/`append_assoc`
friction in Lean 4 and doesn't eliminate indices entirely (the
semantics are inherently positional).

**Index-based (top-down):** Keep lists opaque with `types[i]` and
`types.length`. Add `hQ : A1[n] = Q` as a hypothesis where needed
(every caller has it) to eliminate the S case cheaply. Avoids list
associativity issues. Indices are the natural language for the
positional semantics (`matchesLiteral`, `testWord i clause`, etc.).

Leaning toward consistently index-based as the simpler path. The
decompositional approach has caused more friction than expected
(cons_append, append_assoc), and mixing the two approaches has been
the main source of complexity.

## 5. Cleanup

Delete all `_old` versions, unused helpers, and any lemmas superseded
by whichever approach is chosen.
