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

### Parked / removed
- `testChain_sat_end_lt_new` — removed (no longer present; superseded or abandoned).

## 4. Direction check — RESOLVED

Considered two approaches for simplifying the remaining proofs:

**Decompositional (top-down):** Make Q structural in signatures, pass
list components as separate parameters. Eliminates the S case and
some index boilerplate, but creates `cons_append`/`append_assoc`
friction in Lean 4 and doesn't eliminate indices entirely (the
semantics are inherently positional).

**Index-based (top-down):** Keep lists opaque with `types[i]` and
`types.length`. Add `hQ : A1[n] = Q` as a hypothesis where needed
to eliminate the S case cheaply. Avoids list associativity issues.
Indices are the natural language for the positional semantics
(`matchesLiteral`, `testWord i clause`, etc.).

Leaning toward consistently index-based as the simpler path. The
decompositional approach has caused more friction than expected
(cons_append, append_assoc), and mixing the two approaches has been
the main source of complexity.

### `hQ` hypothesis — REJECTED

Attempted adding `hQ : A1[n] = Q` to `clauseWord_start_nonsat` to
eliminate the S case (~40 lines). The claim "every caller has it" was
wrong: the penalty path (`formulaState_penalty_start` →
`clauseWord_sat.2` / `clauseNext_sat.2`) works with arbitrary `xs`
where `xs[n]` can be S. Threading `hQ` through the entire penalty
path would require restructuring `clauseWord_sat`, `clauseNext_sat`,
`formulaState_penalty_start`, `formulaState_penalty_all`,
`formulaWord_unsat_pos`, and a top-level case split in
`formulaWord_correct'` — too much churn for the benefit.

### Top-down simplification of FormulaWord.lean — DONE

Simplified `formulaWord_correct` by:
- `clauses_ ++ [last]` decomposition (`formulaWord_correct'`) — eliminates
  `clauses.length - 1` arithmetic
- `accepts_iff_applyWord_ext` — absorbs truncation/min plumbing
- Replication helper lemmas (`virtualPileTypes_replicate_Q_snoc`, etc.)
  moved to `VirtualPileTypes.lean`
- `formulaWord_correct` now delegates to `formulaWord_correct'`

## 5. Cleanup

Delete all `_old` versions, unused helpers, and any lemmas superseded
by whichever approach is chosen.

**Status:** `_old` lemmas (`testChain_nactd_old`, `testChain_nactd_end_old`,
`testChain_sat_end_eq_old`) are still in use — not yet deletable.

---

## Gadget lemma restructuring — DONE

Split `activation_correct` into three lemmas matching the structure of
`testWord_consumption_*`, using a membership hypothesis `w ∈ [POS, NEG, DK]`
rather than a conjunction or `Fin 3` index:

- `activation_correct_actd {w} (hw) (st nt)` — equality, any word
- `activation_correct_nactd {w} (hw) (st nt)` — conditional, any word
- `activation_correct_disq {w} (hw) (st nt)` — inequality, any word

Bridge lemmas added to `TestConsume.lean`:
- `testWord_mem` — `testWord i clause ∈ [POS, NEG, DK]`
- `testWord_litMatches` — links `litMatches` to the `(w=POS∧st=Q)∨(w=NEG∧st=S)` condition

`testWord_consumption_actd` and `testWord_consumption_disq` now use the
named gadget lemmas directly (via membership proof `by unfold testWord; split <;> simp`).
`testWord_consumption_nactd` composes `activation_correct_nactd`,
`testWord_mem`, and `testWord_litMatches` via `rw` + `simp only`.

---

## Dep graph tool — DONE (with known limitation)

`tools/graph.lean` + `tools/graph.py`: extracts theorem dependency graph
from elaborated Lean environment, renders via Graphviz.

**Known limitation:** lemmas used only as `simp only [lemma]` arguments
do not appear in `getUsedConstants` on the proof term. The `Syntax`/`InfoTree`
(which does contain these names) is not persisted to `.olean` — it is only
available during elaboration. Workarounds:

- **Option A (done where easy):** replace `simp only [lemma]` with `rw [lemma]`
  or `exact ... lemma ...` to make the reference explicit in the proof term.
  Applied to `satisfiesClause_iff_matchesLiteral` (now uses `exact exists_congr`).
  Not worth the complexity for cases like `testWord_litMatches` (inside `ite`).

- **Option B (future, if needed):** augment `graph.lean` with a source-text
  pass extracting names from `simp [...]` calls. Straightforward regex over
  `.lean` files, but brittle.

- **Option C (future, if annoying):** run the extractor as an elaboration plugin
  (e.g., a `MetaM` command during `lake build`) to access `InfoTree` directly.
  More robust but more complex to set up.

---

## TODO

- **Rework `EndActivation.lean`** analogously to `Activation.lean`: replace
  `endActivationProp` + omnibus `end_activation_correct` with three split lemmas
  by starting position (`end_activation_correct_actd`, `_nactd`, `_disq`), using
  membership hypothesis `{w} (hw : w ∈ [ENDPOS, ENDNEG, ENDDK])`. Then update
  `endTestWord_consumption_*` in `TestConsume.lean` to use the named lemmas
  (eliminating the inline `have gadget := by decide` blocks).
