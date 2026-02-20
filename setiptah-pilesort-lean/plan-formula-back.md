# Plan: `formulaWord_penalty_ext` and backward direction

## Current state

### Already proved
- `formulaWord_correct` backward body: uses `formulaWord_penalty_ext` (sorry) +
  `applyWord_append_truncate` + arithmetic to show `¬∃ vars → ¬accepts`. ✅
- `formulaWord_split`: decomposes `formulaWord n (init ++ [last])` into
  prefix clause+NEXT pairs followed by the last clauseWord. ✅
- `replicate_succ_append`: `List.replicate (m + 1) x = List.replicate m x ++ [x]`. ✅
- `canAccept`: recursive acceptance predicate defined in Reduction.lean. ✅
- VirtualPileTypes helpers: `virtualPileTypes_replicate_Q_comp`, `virtualPileTypes_append`,
  `flatten_replicate_length`, `virtualPileTypes_length`. ✅
- Mono helpers: `applyWord_append`, `applyWord_mono`, `applyWord_ge`,
  `applyWord_append_truncate`, `compile_append_left`. ✅

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

## Organizing principle: `canAccept`

### Definition (already in Reduction.lean)

```lean
def canAccept (n : Nat) (xs : List PileType) (vars : List Bool)
    (prefix_sat : Prop) (clauses_ : List Clause) (last : Clause)
    (start : Nat) : Prop :=
  let types := virtualPileTypes (virtualPileTypes ALIGN xs)
      (List.replicate (clauses_.length + 2) .Q)
  match clauses_ with
  | [] =>
    prefix_sat ∧ satisfiesClause vars last ∧
    applyWord (clauseWord n last) (compile types) start < types.length
  | c :: rest =>
    canAccept n xs vars (prefix_sat ∧ satisfiesClause vars c) rest last
      (applyWord (clauseWord n c ++ NEXT) (compile types) start)
```

Takes `vars` as an explicit parameter — no quantifiers inside the definition.
At each level, types have `clauses_.length + 2` Q-replications (one per
remaining clause in `clauses_`, one for `last`, one vestigial block).

### Unrolling

`canAccept(vars, True, [c₀, ..., c_k], last, 0)` unfolds to:
```
sat(c₀) ∧ sat(c₁) ∧ ... ∧ sat(c_k) ∧ sat(last) ∧ (result < types.length)
```
i.e., `satisfiesFormula vars (clauses_ ++ [last]) ∧ accepted`.

### Key property: changing types at each level

The types shrink by one Q-replication at each recursive step. This means:
- The `mid_state` passed to the recursive call was computed on the outer types
  (with one more block), not the inner types.
- `compile_append_left` bridges this: when the state stays within the smaller
  types' range, the computation on larger types agrees with the smaller types.
- The state always stays within range because:
  - START_POS track: state = j*block < (remaining + 2)*block = types.length ✓
  - CHAIN_DISQ track: state = 1 + j*block < (remaining + 2)*block ✓
    (since block ≥ 6, so 1 < block)

## Two lemmas about `canAccept`

### Lemma 1: `canAccept_of_sat`

```
vars.length = n → xs = embedVars vars ++ [Q] →
  satisfiesFormula vars (clauses_ ++ [last]) →
  start = START_POS + j * block →
  canAccept n xs vars True clauses_ last start
```

**Proof by induction on `clauses_`.**

Each step: `clauseWord_correct` part 1 (clause satisfied) gives
`END_POS + (k+n)*ALIGN.length`, then `next_correct` advances to
`START_POS + (j+1)*block`. The satisfaction conjunction accumulates
via `satisfiesFormula` distributing over the list.

Base case: `clauseWord_correct` part 1 gives result = `END_POS + (k+n)*ALIGN.length`,
which is `< types.length` (types has 2 copies, result is within the first copy).

### Lemma 2: `not_canAccept_bound`

```
(¬prefix_sat ∨ start ≥ CHAIN_DISQ + j * block) →
  applyWord (remaining_formula_word) (compile types) start ≥
    CHAIN_DISQ + (j + clauses_.length + 1) * block
```

This implies `¬canAccept` (since `result ≥ types.length > boundary`) but
also gives the specific numerical bound needed for `formulaWord_penalty_ext`.

**Proof by induction on `clauses_`.**

At each step, two cases:
- **¬prefix_sat or start ≥ CHAIN_DISQ:** By `clauseWord_correct` part 3 +
  `applyWord_mono`, penalty propagates. NEXT preserves via `applyWord_ge`.
  Recurse with `start ≥ CHAIN_DISQ + (j+1)*block`.
- **prefix_sat but clause c unsatisfied (will be handled at assembly):**
  `clauseWord_correct` part 2 triggers penalty. Then recurse as above.

Note: the `¬prefix_sat` case covers both "some previous clause was unsatisfied"
and "xs doesn't encode any valid vars" — `canAccept` doesn't distinguish these.

## Assembly of `formulaWord_penalty_ext`

1. **Split clauses.** `clauses ≠ []` → `∃ init last, clauses = init ++ [last]`
   (via `list_split_last`).

2. **Case analysis on vars.** Since `¬(∃ vars, ... ∧ satisfiesFormula vars clauses)`,
   for any fixed `vars` matching xs, some clause is unsatisfied. In particular,
   either no vars matches xs at all, or the unique matching vars fails some clause.

3. **Apply lemma 2.** Starting from state 0 = START_POS with `prefix_sat = True`:
   - If the first clause is unsatisfied: `prefix_sat ∧ sat(c₀)` becomes
     `True ∧ False = False`, so `¬prefix_sat` at the next level. Lemma 2 applies.
   - If the first clause is satisfied but a later one isn't: `prefix_sat` stays
     true through early clauses (like lemma 1), until the failing clause makes
     it false. Then lemma 2 applies for the remainder.
   - If start ≥ CHAIN_DISQ at any point: lemma 2 applies directly.

   In all cases, `result ≥ CHAIN_DISQ + m * block` on the level-local types.

4. **Connect to full types.** The level-local types at the top level have
   `init.length + 2 = clauses.length + 1` Q copies, matching `types_ext`.
   The computation at the top level IS the computation on `types_ext`.
   So the bound transfers directly.

   For inner levels (smaller types), `applyWord_append_truncate` shows the
   computation on larger types ≥ computation on smaller types (when the
   smaller types' result hits the sink). Since we're proving a lower bound,
   the larger-types result is at least as large.

## Proof order

1. `list_split_last` — split non-empty list into init ++ [last]
2. `satisfiesFormula_append` — `satisfiesFormula vars (A ++ [c]) ↔ satisfiesFormula vars A ∧ satisfiesClause vars c`
3. `canAccept_of_sat` — satisfaction → canAccept (uses clauseWord_correct part 1 + next_correct)
4. `not_canAccept_bound` — penalty conditions → numerical bound (uses clauseWord_correct parts 2/3 + mono)
5. `formulaWord_penalty_ext` — assembly using 1–4 + `formulaWord_split`

## Open question

The exact interaction between changing types and `not_canAccept_bound` needs care.
The bound at each recursive level is stated for that level's types. Connecting
across levels to get the bound on the full `types_ext` requires either:
- Showing the top-level computation directly gives the bound (since the top-level
  types ARE `types_ext`), or
- Using `applyWord_append_truncate` to relate inner-level results to outer-level
  results.

The first option is simpler if the induction is structured so that the top-level
call to `not_canAccept_bound` directly gives the result on `types_ext`.
