# Plan

## `Sortable ↔ automaton accepts` — remaining steps

Main goal: `Sortable d types ↔ applyWord (Deck.changeProfile d) (compile types) 0 < types.length`

Already proved:
- `compile_consecutive` ✅
- `assign_dominates_applyWord` ✅

### Step 0 — `@[ext]` on `Deck` (PileShuffle.lean)
Add `@[ext]` to the `Deck` structure.
Gives: to prove `d1 = d2`, it suffices to prove `d1.posOf = d2.posOf` and `d1.cardAt = d2.cardAt`.

### Step 1 — `strictMono_consec_is_id` (Permutations.lean)
Statement: if `f : Fin n → Fin n` satisfies `∀ k (hk : k+1 < n), f ⟨k,_⟩ < f ⟨k+1,_⟩`,
then `∀ k, f k = k`.

Sub-lemmas (both by induction on k):
- `f_ge`: `∀ k, k.val ≤ (f k).val` — upward: base trivial; step: `f (k+1) > f k ≥ k`
- `f_le`: `∀ k, (f k).val ≤ k.val` — downward: `f (n-1) < n` so `≤ n-1`; step: `f k < f (k+1) ≤ k+1`

Conclude: `f k = k` by `Nat.le_antisymm`.

### Step 2 — `minAssign` definition (SortableIff.lean)
Value: `applyWord ((Deck.changeProfile d).take k.val) (compile types) 0`

Bound proof: `applyWord (take k.val) ... 0 ≤ applyWord word ... 0 < types.length`
- `≤`: `word = take k.val ++ drop k.val`, so `applyWord_append` + `applyWord_ge` on the suffix
- `< types.length`: the acceptance hypothesis

### Step 3 — `minAssign_consecutive` (SortableIff.lean)
For `k+1 < n`:
`(minAssign ⟨k+1,_⟩).val = compile types ((Deck.changeProfile d)[k]) (minAssign ⟨k,_⟩).val`

Proof: unfold both sides via `applyWord_take_succ`.

### Step 4 — `minAssign_sorts` (SortableIff.lean)
Goal: `shuffleRound d types (minAssign d types h) = Deck.sorted n`

a. For each `k+1 < n`: by `minAssign_consecutive` + `changeProfile_get`, get
   `compile types act (minAssign ⟨k,_⟩).val ≤ (minAssign ⟨k+1,_⟩).val`.
   By `compile_consecutive.mpr`: `posOf ⟨k,_⟩ < posOf ⟨k+1,_⟩`.
b. Apply `strictMono_consec_is_id` → `posOf = id`.
c. `cardAt = id`: `cardAt c = cardAt (posOf c) = c` by `left_inv` + step b.
d. `Deck.ext`: closes the goal.

### Step 5 — Main theorem (SortableIff.lean)
```
theorem sortable_iff_accepts {n : Nat} (hn : 0 < n) (d : Deck n) (types : List PileType) :
    Sortable d types ↔ applyWord (Deck.changeProfile d) (compile types) 0 < types.length
```
Note: `0 < n` required — for n=0, LHS is vacuously true but RHS can fail.

Forward (→): `assign_dominates_applyWord` at `k = n-1` gives `applyWord word ... 0 ≤ (assign ⟨n-1,_⟩).val < types.length`. Use `word.take (n-1) = word` (length = n-1).

Backward (←): witness `minAssign d types h`; `minAssign_sorts` closes the goal.

---

## Status

The consumption-form proof stack for `formulaWord_correct` is complete:

- **TestChain.lean** — plain-chain and end-capped consumption lemmas for
  `testWord` sequences.  Design notes and lemma inventory in the module docstring.
- **ClauseWordNew.lean** — `clauseWord_start_sat_cons`, `clauseWord_start_nonsat_cons`,
  `clauseWord_chain_consumption`, plus the representation-mismatch bridge lemmas
  `hasMatchingAssignment_some_matchesLiteral` and `hasMatchingAssignment_activation`.
- **FormulaWordNew.lean** — `clauseNext_good_consumption`, `clauseNext_bad_consumption`,
  `clauseNext_chain_consumption`.
- **FormulaWord.lean** — `formulaWord_correct` proved via the consumption stack.

Old proof machinery has been moved to `Legacy/` or deleted.

## Remaining cleanup

`ClauseWord.lean` still contains two index-form theorems that are dead code:
`testChain_actd` and `testChain_nactd_old`.  Once deleted the file body is empty
and the file itself can be removed (update imports in `FormulaWord.lean` and
`PileSort.lean` accordingly).

## Representation mismatch (open)

The `HasMatchingAssignment` / `embedVars` / `satisfiesClause` layer and the
`matchesLiteral` layer on raw pile types speak different languages.  Bridging
is currently done ad hoc:

- **Positive direction**: `hasMatchingAssignment_some_matchesLiteral` +
  `hasMatchingAssignment_activation` (adapter) in `ClauseWordNew.lean`.
- **Negative direction**: `not_hasMatchingAssignment_no_matchesLiteral` in
  `FormulaWordNew.lean`.

The open question is whether to push the `satisfiesClause`/`HasMatchingAssignment`
vocabulary *down* into the TestChain lemmas (so `testChain_nactd_end_endpos` and
friends accept `HasMatchingAssignment` hypotheses directly), or to keep the bridge
lemmas as a thin adapter layer above TestChain.  The current adapter approach works
and keeps TestChain free of SAT vocabulary; the alternative would shorten the
clauseWord proofs at the cost of coupling TestChain to the reduction layer.

## Index-based vs. destructured forms (open)

The TestChain.lean docstring discusses the two parameterization styles.  The
current lemmas all use the destructured (`A1 ++ A2`) form.  It is worth
investigating empirically whether any call sites would be materially simpler with
the index form, or whether the destructured form is uniformly preferable.  The
conversion between forms is cheap (a length lemma plus `List.take_append_drop`),
so the choice can be revisited per-lemma without cascading changes.

## Naming conventions (open)

Theorem and definition names across the project are inconsistent and do not
always make the content of a lemma obvious from its name.  A naming-convention
pass is planned to make the proof stack easier to navigate.  This is best done
after the representation-mismatch question is settled (since that may rename or
reorganize some of the bridge lemmas).

## Heterogeneous pile facings (future)

A longer-term goal is to develop a mathematical model of pile shuffle that allows
*heterogeneous pile facings*: all cards within a single pile face the same direction
(up or down), but different piles in the same round may have different facings.
The goal is to relate sort feasibility in that model to the main NP-hardness reduction.
This is independent of the current Lean formalization work and can proceed in
parallel once the reduction proof is polished.
