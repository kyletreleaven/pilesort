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

## 3. Sentinel decomposition for `_end` lemmas — IN PROGRESS

Decompose types as `... ++ x :: Q :: A2` where Q is structurally separate,
eliminating `hQ : A1[k+1] = Q` and `hA2 : A2 ≠ []` hypotheses.

### Done so far
- `testChain_nactd_end` — sentinel form compiles (old renamed `_old`)
- `testChain_sat_end_eq` — sentinel form compiles (old renamed `_old`)
- `testChain_sat_end_lt_new` — signature with `sorry`, blocked on 3c

### 3c. Sentinel `testChain_actd_end` and `testChain_activate_end` (NEXT)

`testChain_sat_end_lt_new` needs `testChain_activate_end`, which in turn needs
`testChain_actd_end`. Both are in old form (taking `A1` with `hA1 : A1.length = k+2`,
`hQ : A1[k+1] = Q`). Bridging from sentinel to old form produced ~15 lines of
boilerplate (hlen, hQ indexing, type rewrites).

**Fix:** Write sentinel versions of both:

```
testChain_actd_end (j : Nat) (clause suffix)
    (A1 : List PileType) (x : PileType) (A2 : List PileType) (hA2 : A2 ≠ []) :
    applyWord (... testWords ++ endTestWord ... ++ suffix)
      (compile (vpt ALIGN (A1 ++ x :: Q :: A2))) ACTD =
    (A1.length + 1) * m + applyWord suffix (vpt ALIGN (Q :: A2)) END_POS
```

This requires `testChain_actd` in consumption form (analogous to `testChain_nactd`).
Currently `testChain_actd` uses `types.drop k` in its conclusion.

**Order:**
1. `testChain_actd` consumption form (A1 ++ A2, induction on A1)
2. `testChain_actd_end` sentinel form (A1 ++ x :: Q :: A2)
3. `testChain_activate_end` sentinel form (x :: A1_post ++ Q :: A2)
4. `testChain_sat_end_lt_new` — fill in sorry (should be short: split range,
   testChain_nactd, testChain_activate_end, arithmetic)

### 3d. `testChain_sat_end` combiner — after 3c

Combine `testChain_sat_end_lt_new` and `testChain_sat_end_eq` into a single
dispatcher with sentinel form.

### 3e. Propagate to `clauseWord_start_nonsat`

Drop A0 param. Take `A1 ++ Q :: A2` structurally. The S case (~40 lines)
vanishes because no caller ever passes A1 with last element S — the machine
is always built with Q sentinels.

### 3f. Propagate to `clauseWord_start_sat`

Similarly, take `embedVars vars` and Q structurally.

## 4. Inline `list_drop_append_two_last` — deferred

Only used once (in `clauseWord_start_nonsat`). Will become unnecessary after #3e.

## 5. Inline `testChain_activate_end_split` — deferred

Only used once (in old `testChain_sat_end_lt`). Will become unnecessary after #3c.

## 6. Cleanup

Delete all `_old` versions, `testChain_nactd_split`, `testChain_activate_end_split`,
and any list helper lemmas that become unused (`list_drop_two`, `list_drop_append_two`,
`list_drop_append_two_last`).
