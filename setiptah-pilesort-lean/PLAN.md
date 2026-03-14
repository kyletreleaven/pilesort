# Plan

## Cleanup: remove old FormulaWord machinery

Most of this has already been deleted. Remaining items still in the codebase:

- `next_correct_rep` in `FormulaWord.lean`
- `virtualPileTypes_replicate_Q_cons'` (and variant) in `FormulaWord.lean`
- `formulaState` definition in `Reduction.lean`

`not_satisfiesFormula_rest` must stay (used in `formulaWord_unsat_pos'`).

## TestChain.lean (done)

`TestChain.lean` holds consumption-form lemmas for `testWord` sequences.
All three plain-chain lemmas are complete:

- `testChain_actd_cons`: from ACTD, shifts past A1, stays ACTD (= form)
- `testChain_disq_cons`: from CLAUSE\_DISQ, shifts past A1, stays ≥ CLAUSE\_DISQ
- `testChain_nactd_cons`: from NACTD, shifts past A1, lands at ACTD or NACTD
  depending on `∃ i : Fin A1.length, matchesLiteral A1[i] (start+i) clause`

End-capped lemmas (`testWords ++ endTestWord`) also in `TestChain.lean`:

- `testChain_disq_end'`: from CLAUSE\_DISQ, k testWords + endTestWord → ≥ CHAIN\_DISQ
- `testChain_actd_end_new`: from ACTD, Q sentinel hardcoded → = END\_POS
- `testChain_actd_end_disq`: from ACTD, `et ≠ Q` → ≥ CHAIN\_DISQ

Still needed: NACTD end-capped lemmas (see "NACTD end-capped" section above).

## End-capped TestChain lemmas (TestChain.lean)

`TestChain.lean` now also holds end-capped lemmas: `testWords ++ endTestWord ++ suffix`
from a given starting state, in consumption form.  Already proved:

- `testChain_disq_end'` (from CLAUSE_DISQ → ≥ CHAIN_DISQ, A1.length = k+2 form)
- `testChain_actd_end_new` (from ACTD, Q sentinel hardcoded → = END_POS)
- `testChain_actd_end_disq` (from ACTD, non-Q sentinel `et ≠ Q` → ≥ CHAIN_DISQ)

Still needed: NACTD end-capped lemmas.

### NACTD end-capped: 2 vs 3 lemmas

The NACTD case has three outcome sub-cases:

1. **Chain activates + Q sentinel** → END_POS  (use `testChain_actd_end_new` after chain)
2. **No chain activation + Q sentinel + end matches** → END_POS  (`endTestWord_consumption_nactd` sat branch)
3. **No chain activation + Q sentinel + no end match** → ≥ CHAIN_DISQ
4. **Non-Q sentinel** (regardless of chain) → ≥ CHAIN_DISQ  (use `testChain_actd_end_disq` or `applyWord_mono` + end lemma)

**Option A — 3 lemmas** (split disq by sentinel type):
- `testChain_nactd_end_endpos`: Q sentinel + any activation → = END_POS
- `testChain_nactd_end_disq_nomatch`: Q sentinel + no activation anywhere → ≥ CHAIN_DISQ
- `testChain_nactd_end_disq_noQ`: non-Q sentinel → ≥ CHAIN_DISQ

  Pro: each lemma has a single clean hypothesis; maps 1-1 onto the three branches
  of `clauseWord_start_nonsat_cons` (Q case, S case) and `clauseWord_start_sat_cons`.
  Con: `clauseWord_start_nonsat_cons` still requires an internal Q/S case split.

**Option B — 2 lemmas** (combine disq cases):
- `testChain_nactd_end_endpos`: Q sentinel + any activation → = END_POS
- `testChain_nactd_end_disq`: no activation OR non-Q sentinel → ≥ CHAIN_DISQ
  (handles Q/S split internally)

  Pro: `clauseWord_start_nonsat_cons` needs no case split — applies `testChain_nactd_end_disq`
  directly from the `¬HasMatchingAssignment` hypothesis.
  Con: `testChain_nactd_end_disq` is internally more complex (two sub-cases).

**Verdict: open.**  Option B gives cleaner clauseWord proofs; Option A spreads
complexity more evenly.  The right choice depends on whether the combined disq
proof is unwieldy.  Recommend trying Option B first; fall back to A if the
internal case split in `testChain_nactd_end_disq` proves painful.

## Step 2: clauseWord consumption-form lemmas

Re-prove (or prove anew) the two clauseWord consumption-form lemmas using only
the clean building blocks: `start_clause_*`, TestChain lemmas, and the
individual `endTestWord_consumption_*` lemmas. The existing
`clauseWord_start_consumption` and `clauseWord_chain_consumption` in
`ClauseWordCorrect.lean` are the target statements; the goal is to simplify
their proofs.

### Prerequisites (already exist)

`start_clause_start` and `start_clause_disq` in `StartClause.lean` are the
single-origin consumption-form lemmas for the START_CLAUSE gadget — proved via
`gadget_lift_*` + `decide`. No changes needed there.

### clauseWord from START_POS (`clauseWord_start_consumption`)

Proof structure:
1. `start_clause_start` → suffix sees machine from NACTD
2. NACTD TestChain lemma → suffix sees A2 from ACTD (sat) or NACTD (nonsat)
3. `endTestWord_consumption_nactd` (sat/nonsat) or `endTestWord_consumption_actd`

Note: the current proof uses a classical case split (`HasMatchingAssignment`)
and `satisfiesClause_first_matchesLiteral` to find the first activation index.
This logic will need to connect to the existential in the NACTD TestChain lemma.

### clauseWord from CHAIN_DISQ (`clauseWord_chain_consumption`)

Proof structure:
1. `start_clause_disq` → suffix sees machine from ≥ CLAUSE_DISQ
2. CLAUSE_DISQ TestChain lemma → suffix sees A2 from ≥ CLAUSE_DISQ
3. `endTestWord_consumption_disq`

Note: `applyWord_mono` bridges the `≥ CLAUSE_DISQ` output of `start_clause_disq`
into the CLAUSE_DISQ TestChain lemma — same pattern as the current proof.

## Step 3: clauseNext consumption-form lemmas

Re-prove (or prove anew) the three `clauseNext` consumption-form lemmas in
`FormulaWordNew.lean` using only the clauseWord consumption lemmas from Step 2.
The target lemmas are:

- `clauseNext_good_consumption` (from START_POS)
- `clauseNext_bad_consumption` (from START_POS, unsatisfied clause)
- `clauseNext_chain_consumption` (from CHAIN_DISQ)

Each should reduce to a single `clauseWord_start_consumption` or
`clauseWord_chain_consumption` application (from Step 2), plus arithmetic.

## Step 4: Cleanup / deletion

Once Steps 1–3 are complete and the build passes, delete all dead code that is
no longer on the proof path of `formulaWord_correct`:

- Everything listed under "Cleanup: remove old FormulaWord machinery" above
- `testChain_nactd_old`, `testChain_nactd_end_old`, `testChain_sat_end_eq_old`
  in `ClauseWord.lean` (check uses first)
- Any remaining uses of bundled `testWord_consumption` / `endTestWord_consumption`
  (already eliminated, but confirm the definitions can be deleted too)
- Any other lemmas rendered unreachable by the new proof stack

---

## Progress

- [x] **Step 1a** — `testChain_actd_cons` in `TestChain.lean`
- [x] **Step 1b** — `testChain_disq_cons` (A1++A2 form) in `TestChain.lean`
- [x] **Step 1c** — `testChain_nactd_cons` in `TestChain.lean`
- [x] **Step 1d** — End-capped lemmas in `TestChain.lean`:
  - [x] `testChain_disq_end'` (migrated + reproved from `testChain_disq_cons`)
  - [x] `testChain_actd_end_new` (migrated from `ClauseWord.lean`)
  - [x] `testChain_actd_end_disq` (new)
  - [ ] `testChain_nactd_end_endpos` (NACTD → END\_POS)
  - [ ] `testChain_nactd_end_disq` (NACTD → ≥ CHAIN\_DISQ; see plan above)
- [ ] **Step 2a** — Re-prove `clauseWord_start_consumption` using TestChain lemmas
  - [x] `clauseWord_start_nonsat_cons` (in `ClauseWordNew.lean`)
  - [ ] `clauseWord_start_sat_cons`
  - [ ] delegating `clauseWord_start_consumption`
- [x] **Step 2b** — `clauseWord_chain_consumption` (in `ClauseWordNew.lean`)
- [ ] **Step 3a** — Re-prove `clauseNext_good_consumption`
- [ ] **Step 3b** — Re-prove `clauseNext_bad_consumption`
- [ ] **Step 3c** — Re-prove `clauseNext_chain_consumption`
- [ ] **Step 4**  — Delete dead code; confirm clean build

### Dead code (pending Step 4 deletion)
In `ClauseWordCorrect.lean`: `testChain_disq`, `testChain_disq_end`
In `ClauseWord.lean`: `testChain_actd`, `testChain_actd_end`, `testChain_activate_end_new`,
  `testChain_activate_end`, `testChain_nactd_old`, `testChain_nactd`, `testChain_nactd_split`,
  `testChain_activate_end_split`, `testChain_nactd_end_old`, `testChain_nactd_end`,
  `testChain_sat_end_lt`, `testChain_sat_end_eq`, `testChain_sat_end_eq_old`,
  `testChain_sat_end`, `testChain_sat_end_zero`
  (verify each before deleting)

### Completed prerequisites
- [x] All bundled `testWord_consumption` / `endTestWord_consumption` call sites
      replaced with individual `_actd` / `_nactd` / `_disq` variants
- [x] `start_clause_start` and `start_clause_disq` in `StartClause.lean`

