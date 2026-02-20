# Plan: `formulaWord_penalty_ext` and backward direction

## Current state

### Already proved
- `formulaWord_correct` backward body: uses `formulaWord_penalty_ext` (sorry) +
  `applyWord_append_truncate` + arithmetic to show `¬∃ vars → ¬accepts`. ✅
- `formulaWord_split`: decomposes `formulaWord n (init ++ [last])` into
  prefix clause+NEXT pairs followed by the last clauseWord. ✅
- `replicate_succ_append`: `List.replicate (m + 1) x = List.replicate m x ++ [x]`. ✅
- `formulaState`: tail-recursive endpoint computation defined in Reduction.lean. ✅
- VirtualPileTypes helpers: `virtualPileTypes_replicate_Q_comp`, `virtualPileTypes_append`,
  `flatten_replicate_length`, `virtualPileTypes_length`. ✅
- Mono helpers: `applyWord_append`, `applyWord_mono`, `applyWord_ge`,
  `applyWord_append_truncate`, `compile_append_left`, `compile_append_right`. ✅

### Remaining sorry
- `formulaWord_penalty_ext` — the main lemma (this plan)
- `formulaWord_forward` — forward direction (separate plan)
- `clauseWord_correct` — clause-level gadget composition (separate plan)

## Goal of `formulaWord_penalty_ext`

```
¬(∃ vars, vars.length = n ∧ xs = embedVars vars ++ [Q] ∧ satisfiesFormula vars clauses) →
  applyWord (formulaWord n clauses) (compile types_ext) 0 ≥
    CHAIN_DISQ + clauses.length * xs.length * ALIGN.length
```

where `types_ext = virtualPileTypes ALIGN (replicate (clauses.length + 1) xs).flatten`.

## Organizing principle: `formulaState`

### Definition (in Reduction.lean)

```lean
def formulaState (n : Nat) (xs : List PileType)
    (clauses_ : List Clause) (last : Clause) (start : Nat) : Nat :=
  let types := virtualPileTypes (virtualPileTypes ALIGN xs)
      (List.replicate (clauses_.length + 2) .Q)
  let block := xs.length * ALIGN.length
  match clauses_ with
  | [] => applyWord (clauseWord n last) (compile types) start
  | c :: rest =>
    block + formulaState n xs rest last
      (applyWord (clauseWord n c ++ NEXT) (compile types) start - block)
```

Tail-recursive computation of the formulaWord endpoint. At each level,
types have `clauses_.length + 2` Q-replications (remaining + last + vestigial).

The recursive case peels off one clause and adds one block to the result.
The `- block` adjusts the mid state from outer-types coordinates to
inner-types coordinates (justified by `compile_append_right`: outer types =
one block ++ inner types, so positions shift by exactly one block).

### Key state transitions per clause

Let `block = xs.length * ALIGN.length`, `mid = applyWord(clauseWord c ++ NEXT)(compile types)(start)`.

- `start = START_POS`, clause satisfied: `mid = block + START_POS`
  → inner start = `START_POS` (good track preserved)
- `start = START_POS`, clause unsatisfied: `mid ≥ block + CHAIN_DISQ`
  → inner start `≥ CHAIN_DISQ` (shifts to penalty track)
- `start ≥ CHAIN_DISQ`: part 3 + mono → `mid ≥ block + CHAIN_DISQ`
  → inner start `≥ CHAIN_DISQ` (penalty propagates)

### Total result

`formulaState(init, last, 0)` accumulates `init.length * block + base_result`:

- **All satisfied:** base at `START_POS`, result = `END_POS + n*ALIGN.length < block`
  → total `< m * block` (accepted)
- **Some clause failed:** base at `≥ CHAIN_DISQ`, result `≥ CHAIN_DISQ + block`
  → total `≥ m * block + CHAIN_DISQ` (penalty) ✓

## Lemmas to prove

### 1. `applyWord_compile_append_shift`

```
applyWord word (compile (A ++ B)) (A.length + s) = A.length + applyWord word (compile B) s
```

Follows from `compile_append_right` by induction on `word`. This is the
shift lemma that justifies `formulaState`'s recursive structure.

### 2. `formulaState_eq` (equivalence)

```
formulaState n xs init last 0 = applyWord (formulaWord n (init ++ [last])) (compile types_ext) 0
```

where `types_ext` has `init.length + 2` Q-replications (matching the top level).
Proof by induction on `init`, using `formulaWord_split`, `applyWord_append`,
and the shift lemma.

### 3. `formulaState_forward`

```
vars.length = n → xs = embedVars vars ++ [Q] →
  satisfiesFormula vars (clauses_ ++ [last]) →
  start = START_POS →
  formulaState n xs clauses_ last start < xs.length * ALIGN.length
```

i.e., when all clauses satisfied and starting from START_POS, the base-level
result (before block accumulation) is < block, so the total is
`init.length * block + (something < block)`.

Proof by induction on `clauses_`. Each step: `clauseWord_correct` part 1
gives `END_POS + (k+n)*ALIGN.length`, then `next_correct` advances to
`START_POS + block`, so inner start = `START_POS`. Recurse.

### 4. `formulaState_penalty`

```
start ≥ CHAIN_DISQ →
  formulaState n xs clauses_ last start ≥
    clauses_.length * block + CHAIN_DISQ + block
```

i.e., once on the penalty track, the base-level result is ≥ CHAIN_DISQ + block,
and each peeled clause adds a block. Total ≥ `(clauses_.length + 1) * block + CHAIN_DISQ`.

Proof by induction on `clauses_`. Each step: `clauseWord_correct` part 3 +
`applyWord_mono` gives `mid ≥ block + CHAIN_DISQ`, so inner start `≥ CHAIN_DISQ`.
Recurse.

### 5. `satisfiesFormula_append`

```
satisfiesFormula vars (A ++ [c]) ↔ satisfiesFormula vars A ∧ satisfiesClause vars c
```

Small lemma, `simp [satisfiesFormula, List.mem_append]` or similar.

### 6. `list_split_last`

```
clauses ≠ [] → ∃ init last, clauses = init ++ [last] ∧ init.length + 1 = clauses.length
```

## Assembly of `formulaWord_penalty_ext`

1. **Split** `clauses = init ++ [last]` via `list_split_last`.

2. **Rewrite** via `formulaState_eq`:
   `applyWord (formulaWord n clauses) (compile types_ext) 0 = formulaState n xs init last 0`

3. **Case analysis.** Since `¬(∃ vars, ... ∧ satisfiesFormula vars clauses)`:
   - If no vars matches xs: every clause triggers part 2. The first clause
     shifts inner start to `≥ CHAIN_DISQ`. Apply `formulaState_penalty` to
     the remaining clauses.
   - If unique vars matches xs but fails some clause j: clauses before j
     are satisfied (inner start stays `START_POS`). Clause j shifts to
     `≥ CHAIN_DISQ`. Apply `formulaState_penalty` to the rest.
   In both cases: `formulaState ≥ m * block + CHAIN_DISQ`. ✓

   More precisely: the first unsatisfied clause gives a `formulaState` that
   decomposes as `j * block + formulaState(remaining, last, ≥ CHAIN_DISQ)`.
   By `formulaState_penalty`: `formulaState(remaining, ...) ≥ (m - j) * block + CHAIN_DISQ`.
   Total: `j * block + (m - j) * block + CHAIN_DISQ = m * block + CHAIN_DISQ`. ✓

## Proof order

1. `applyWord_compile_append_shift` — shift lemma (in Mono.lean)
2. `formulaState_eq` — equivalence to applyWord
3. `satisfiesFormula_append` — small helper
4. `list_split_last` — small helper
5. `formulaState_forward` — forward case (by induction, uses clauseWord_correct part 1)
6. `formulaState_penalty` — penalty case (by induction, uses clauseWord_correct part 3)
7. `formulaWord_penalty_ext` — assembly
