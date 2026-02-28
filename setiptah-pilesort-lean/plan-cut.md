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
testChain_nactd (A1 : List PileType) (x : PileType) (A2 : List PileType)
    (start : Nat) (clause suffix)
    (hno : ∀ i (hi : i < A1.length), ¬matchesLiteral (A1[i]) (start + i) clause) :
    applyWord (range' start A1.length ...) (compile (vpt ALIGN (A1 ++ x :: A2))) NACTD =
    A1.length * ALIGN.length + applyWord suffix (compile (vpt ALIGN (x :: A2))) NACTD
```

The `x :: A2` form makes the tail structurally non-empty — no `hA2 : A2 ≠ []` needed,
since `testWord_consumption` requires `rest ≠ []` and `A1_rest ++ x :: A2` is always
non-empty.

**Proof:** Induction on `A1` (nil/cons). Cons case: `testWord_consumption` on head
with rest = `A1_rest ++ x :: A2` (non-empty for free), recurse on tail.

**Eliminates:**
- `testChain_nactd_split` (lines 182-193) — was the `A1 ++ A2` adapter
- `list_drop_append_two` calls at downstream sites (no more `drop` in the conclusion)
- `getElem_append_left` conversions in `testChain_nactd_end`

**Consistency:** Makes `testChain_nactd` match the consumption pattern used by
`testWord_consumption`, `endTestWord_consumption`, `testChain_actd`, `testChain_disq` —
all consume from the front and state what's left. Currently `testChain_nactd` is
the odd one out with its `types.drop k` conclusion.

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
