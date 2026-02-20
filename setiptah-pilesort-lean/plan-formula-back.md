# Plan: `formulaWord_penalty_ext` and backward direction

## Current state

### Already proved
- `formulaWord_correct` backward body: uses `formulaWord_penalty_ext` (sorry) +
  `applyWord_append_truncate` + arithmetic to show `¬∃ vars → ¬accepts`. ✅
- `formulaWord_split`: `formulaWord n (init ++ [last]) = (init.flatMap (fun c => clauseWord n c ++ NEXT)) ++ clauseWord n last`. ✅
- `replicate_succ_append`: `List.replicate (m + 1) x = List.replicate m x ++ [x]`. ✅
- VirtualPileTypes helpers: `virtualPileTypes_replicate_Q_comp`, `virtualPileTypes_append`,
  `flatten_replicate_length`, `virtualPileTypes_length`. ✅
- Mono helpers: `applyWord_append`, `applyWord_mono`, `applyWord_ge`,
  `applyWord_append_truncate`. ✅

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

## Strategy: split into prefix + last clauseWord

Using `formulaWord_split`, decompose `formulaWord n clauses` into:
```
(init.flatMap (fun c => clauseWord n c ++ NEXT)) ++ clauseWord n last
```
where `clauses = init ++ [last]`.

By `applyWord_append`, the result splits: process the prefix from state 0,
then process the last clauseWord from the resulting state.

This avoids the off-by-1 problem: working with the full word (all clauses with
trailing NEXT) would give `fullWord_result ≥ CHAIN_DISQ + m*block`, but
`formulaWord_result ≥ fullWord_result - 1` (from `compile_step_le`), losing
exactly `CHAIN_DISQ = 1`. By ending with a bare clauseWord instead, parts 2/3
of `clauseWord_correct` give the bound directly.

## Helper lemmas needed

### 1. `list_split_last` (list manipulation)

```
clauses ≠ [] → ∃ init last, clauses = init ++ [last] ∧ init.length + 1 = clauses.length
```

Standard list fact. Proof by cases on `clauses.reverse` or induction.

### 2. `satisfiesFormula_append` (definition unfolding)

```
satisfiesFormula vars (init ++ [last]) ↔
  satisfiesFormula vars init ∧ satisfiesClause vars last
```

Needed to decompose the `¬∃` hypothesis: if ¬(∃ vars satisfying all clauses),
and all init clauses are satisfied, then the last clause must fail.

### 3. `prefix_invariant` (main inductive lemma)

After processing `j` clause+NEXT pairs on `types_ext` starting from state 0:

```
let s := applyWord (cs.flatMap (fun c => clauseWord n c ++ NEXT)) (compile types_ext) 0
let block := xs.length * ALIGN.length
(s = START_POS + j * block
  ∧ ∃ vars, vars.length = n ∧ xs = embedVars vars ++ [Q] ∧ satisfiesFormula vars cs)
∨ (s ≥ CHAIN_DISQ + j * block)
```

where `j = cs.length` and types_ext has enough blocks (≥ j + 2 copies of xs).

**Proof by induction on cs.**

**Base case (cs = []):** s = 0 = START_POS. Left disjunct holds with
`satisfiesFormula vars []` vacuously true (if ∃ matching vars) or right
disjunct holds vacuously (0 ≥ CHAIN_DISQ + 0? No, 0 < 1). So we need the
left disjunct. The ∃ vars condition: either some vars matches xs, in which
case left holds, or no vars matches, in which case... hmm.

**Revised base case:** Actually, the left disjunct requires ∃ vars with
`xs = embedVars vars ++ [Q]`. If xs has no such form, neither disjunct
holds at j=0 since s=0 < CHAIN_DISQ=1. So the invariant needs adjustment.

**Better formulation:**
```
(s = START_POS + j * block)
∨ (s ≥ CHAIN_DISQ + j * block)
```

Drop the satisfaction condition from the disjunction. The satisfaction
information is only needed at the final step (to know which case applies
to the last clause). Handle it there using the global ¬∃ hypothesis.

**Base case:** s = 0 = START_POS + 0*block. Left disjunct. ✓

**Inductive step (cs = cs' ++ [c]):** Given invariant for cs', prove for cs.
Process clauseWord(c) + NEXT:

- **From left (s = START_POS + j*block):**
  Apply `clauseWord_correct` with A0 = (replicate j xs).flatten, A1 = xs,
  A2 = remaining copies. k = j*xs.length.
  - Part 1 (∃ satisfying vars for c): → END_POS + (k+n)*align_len.
    Then `next_correct`: → START_POS + (k+n+1)*align_len = START_POS + (j+1)*block.
    Left disjunct for j+1. ✓
  - Part 2 (no satisfying vars for c): → ≥ CHAIN_DISQ + (k+n+1)*align_len
    = CHAIN_DISQ + (j+1)*block. Then `applyWord_ge` for NEXT preserves bound.
    Right disjunct for j+1. ✓

- **From right (s ≥ CHAIN_DISQ + j*block):**
  By `applyWord_mono`, result ≥ result starting from CHAIN_DISQ + j*block.
  `clauseWord_correct` part 3: → ≥ CHAIN_DISQ + (k+n+1)*align_len = CHAIN_DISQ + (j+1)*block.
  Then `applyWord_ge` for NEXT preserves bound.
  Right disjunct for j+1. ✓

### 4. Assembly of `formulaWord_penalty_ext`

Given `clauses ≠ []` (implied by the types having `clauses.length + 1` blocks):

1. Split `clauses = init ++ [last]` using `list_split_last`.
2. Rewrite with `formulaWord_split`: word = prefix ++ clauseWord(last).
3. Apply `applyWord_append` to get intermediate state `s_mid`.
4. Apply `prefix_invariant` to get `s_mid` is either START_POS or ≥ CHAIN_DISQ
   at offset `init.length * block`.
5. Apply `clauseWord_correct` to the last clause:
   - **From right (s_mid ≥ CHAIN_DISQ + init.length*block):**
     Part 3 → ≥ CHAIN_DISQ + m*block. Done.
   - **From left (s_mid = START_POS + init.length*block):**
     Need to show part 2's condition holds for `last`. From `¬(∃ vars, ... ∧
     satisfiesFormula vars clauses)` and `satisfiesFormula_append`, if there
     were vars satisfying all init clauses AND `last`, that would contradict
     the hypothesis. But we need the stronger statement: there's no vars
     matching xs that satisfies `last` (part 2's exact condition).

     Two sub-cases:
     - xs has no matching vars at all: part 2 holds trivially.
     - xs = embedVars(vars) ++ [Q] for unique vars: if vars satisfied all
       init clauses but not last, part 2 holds. If vars didn't satisfy some
       init clause, we'd be in the right disjunct already (contradiction
       with being in the left). So vars must have satisfied all init clauses,
       hence must fail on last.

     Either way, part 2 → ≥ CHAIN_DISQ + m*block. Done.

## Proof order

1. `list_split_last` — small list lemma
2. `satisfiesFormula_append` — definition unfolding
3. `prefix_invariant` — main inductive argument (most work)
4. `formulaWord_penalty_ext` — assembly using 1-3 + `formulaWord_split`
