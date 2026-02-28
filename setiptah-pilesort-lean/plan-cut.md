# Plan: Simplify ClauseWord.lean

## 1. Eliminate getD/getElem bridge lemmas — DONE

Restated `satisfiesClause_first_matchesLiteral` to use `Fin vars.length` and
`embedVar vars[i₀]` directly. Dropped `n`/`hvars` params; used `Nat.strongRecOn`.

**Eliminated:**
- `matchesLiteral_embedVars_getD`
- `matchesLiteral_getD_eq_getElem`
- `List.getD_eq_getElem`

Net: -17 lines (851 → 834).

## 2. Restate `testChain_nactd` in consumption form

Restate `testChain_nactd` to take `A1 ++ A2` where `A1` is the non-matching prefix,
with conclusion mentioning `A2` directly instead of `types.drop k`.

**New signature:**
```
testChain_nactd (A1 A2 : List PileType) (start : Nat) (clause suffix) (hA2 : A2 ≠ [])
    (hno : ∀ i (hi : i < A1.length), ¬matchesLiteral (A1[i]) (start + i) clause) :
    applyWord (range' start A1.length ...) (compile (vpt ALIGN (A1 ++ A2))) NACTD =
    A1.length * ALIGN.length + applyWord suffix (compile (vpt ALIGN A2)) NACTD
```

**Proof:** Induction on `A1` (nil/cons). Cons case: `testWord_consumption` on head
with rest = `A1_rest ++ A2` (non-empty since A2 ≠ []), recurse on tail.

**Eliminates:**
- `testChain_nactd_split` — was the `A1 ++ A2` adapter
- `list_drop_append_two` calls at downstream sites (no more `drop` in the conclusion)
- `getElem_append_left` conversions in `testChain_nactd_end`

**Consistency:** Makes `testChain_nactd` match the consumption pattern used by
`testWord_consumption`, `endTestWord_consumption`, `testChain_actd`, `testChain_disq`.

## 3. Sentinel decomposition for `_end` lemmas — IN PROGRESS

Currently `testChain_nactd_end`, `testChain_sat_end`, etc. take `A1 A2` where
A1 contains both the variable pile types AND the sentinel Q as its last element
(accessed via `A1[k+1]`), and `hA2 : A2 ≠ []`.

More natural: decompose as `A1 ++ Q :: A2` where:
- `A1` = variable pile types (length n)
- `Q` = sentinel (structurally separate, no indexing needed)
- `A2` = rest of the machine (non-emptiness is free)

This eliminates `hQ : A1[k+1] = Q` and `hA2 : A2 ≠ []` hypotheses, and avoids
indexing into the end of A1 to find the sentinel.

**Done so far:** new `testChain_nactd` (A1 ++ A2 form) and new `testChain_nactd_end`
(sentinel form) both compile. Old versions renamed `_old`.

**Depends on:** #2 (testChain_nactd restatement), since the `_end` lemmas call it.
**Affects:** `testChain_nactd_end`, `testChain_sat_end_lt`, `testChain_sat_end_eq`,
`testChain_sat_end`, `testChain_sat_end_zero`, and their consumers
(`clauseWord_start_sat`, `clauseWord_start_nonsat`).

### 3a. Propagate sentinel decomposition to `clauseWord_start_nonsat`

`clauseWord_start_nonsat` takes `A0 A1 A2` but:
- A0 is factored out immediately via `clauseWord_start_preamble` (shift lemma).
  A0 doesn't belong in the signature — the caller can handle the shift.
- A1 (length n+1) is case-split on `A1[n]` (Q vs S). The S case exists only because
  A1 might not end in Q. If we take the sentinel Q structurally, the S case vanishes.

**Proposed new form:** Drop A0. Take `A1 : List PileType` (length n, the variables)
and `A2 : List PileType`. Types are `A1 ++ Q :: A2`.

Then:
- `hQ` disappears (structural)
- `hA2 : A2 ≠ []` disappears (structural non-emptiness of `Q :: A2`)
- The S case (lines 628-668) disappears entirely. Currently `clauseWord_start_nonsat`
  case-splits on `A1[n]`: Q or S. The S case proves the penalty bound via a
  monotonicity argument (NACTD ≥ ACTD, then `testChain_actd` + `endTestWord_actd_bad`).
  But this case only exists because the old signature allows `A1[n]` to be anything.
  No caller ever passes an A1 whose last element is S — the machine is always built
  with Q sentinels. Making Q structural eliminates a ~40-line proof branch that was
  correct but unnecessary.
- `not_hasMatchingAssignment_no_matchesLiteral` works on `A1 ++ [Q]` directly
- Calling new `testChain_nactd_end` is direct (A1 is the prefix, Q is the sentinel)

The caller (`clauseWord_correct`) can decompose its `A1` (length n+1) into
`A1.take n ++ [Q]` and regroup as `A1.take n ++ Q :: A2` using list associativity.

### 3b. Same treatment for `clauseWord_start_sat`

Similarly, `clauseWord_start_sat` takes `A0 A1 A2`. After factoring out A0,
it substitutes `A1 = embedVars vars ++ [Q]` and calls `testChain_sat_end_zero`.
With sentinel form, A1 would be `embedVars vars` directly and Q structural.

## 4. Inline `list_drop_append_two_last` — easy win

Only used once (in `clauseWord_start_nonsat`). Inline it and delete the lemma.
May become unnecessary after #3.

## 5. Inline `testChain_activate_end_split` — easy win

Only used once (in `testChain_sat_end_lt`). Thin wrapper around
`testChain_activate_end` that converts `getElem_drop`. Could inline.
May become unnecessary after #3.

## 6. Merge `testChain_sat_end_lt` and `testChain_sat_end_eq` — speculative

Different proof machinery. May not simplify. Revisit after #3.

## 6. (Closed) Simplify `satisfiesClause_first_matchesLiteral` proof — DONE in #1

Replaced verbose bound-based induction with `Nat.strongRecOn` (20 lines vs 30).
