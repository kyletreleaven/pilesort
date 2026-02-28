# Plan: endTestWord_consumption

## Project context

- **Lean project root**: `/Users/ktreleav/workspaces/setiptah-pilesort/setiptah-pilesort-lean/`
- **Build command**: `cd <root> && ~/.elan/bin/lake build`
- **Lean version**: 4.16.0, NO Mathlib

### Key files
- `PileSort/TestConsume.lean` — where `endTestWord_consumption` lives (the theorem to prove)
  - Also contains `litMatches`, `matchesLiteral`, and the proved `testWord_consumption_*` lemmas (use as templates)
- `PileSort/Reduction.lean` — `LitPresence`, `Clause`, `testWord`, `endTestWord`, `satisfiesClause`
- `PileSort/Words.lean` — word constants (POS, NEG, DK, ENDPOS, ENDNEG, ENDDK) and position constants
- `PileSort/Gadgets/Lifting.lean` — `gadget_lift_eq`, `gadget_lift_ge`
- `PileSort/Gadgets/EndActivation.lean` — `endActivationProp`, `end_activation_correct` (gadget-level facts for endTestWord, proved by `decide`)
- `PileSort/Mono.lean` — `applyWord_mono`, `applyWord_compile_append_shift`, `applyWord_append`
- `PileSort/VirtualPileTypes.lean` — `virtualPileTypes`, `virtualPileTypes_append`, `virtualPileTypes_length`

### Key constants (from Words.lean)
- Positions: START_POS=0, CHAIN_DISQ=1, ACTD=2, NACTD=3, END_POS=5, CLAUSE_DISQ=5
- ALIGN.length = 6
- `endTestWord i clause` = match clause.getD i .absent with .pos => ENDPOS | .neg => ENDNEG | .absent => ENDDK

### Key definitions
- `litMatches (lp : LitPresence) (x : PileType) := (lp = .pos ∧ x = .Q) ∨ (lp = .neg ∧ x = .S)`
- `matchesLiteral x i clause := litMatches (clause.getD i .absent) x`
- `virtualPileTypes ALIGN types` has length `types.length * ALIGN.length`

### Proved template: testWord_consumption_actd (equality case)
```lean
-- 1. Gadget helper by decide
have gadget : ∀ (lp : LitPresence) (st nt : PileType), ... := by decide
-- 2. Decompose rest = y :: rest'
obtain ⟨y, rest', rfl⟩ ...
-- 3. Specialize: unfold testWord; exact gadget (clause.getD i .absent) x y
-- 4. Lift: gadget_lift_eq ... [] [x, y] rest' ...
-- 5. applyWord_append, substitute, shift via applyWord_compile_append_shift
```

### Proved template: testWord_consumption_disq (inequality case)
Same as above but uses `gadget_lift_ge` and needs `applyWord_mono` + `calc` chain.

### Pitfalls discovered during testWord proofs
- `decide` can't handle free variables — use `omega` not `decide` for arithmetic goals containing `if matchesLiteral ...`
- After `gadget_lift_eq` with A=[], need `simp only [List.cons_append, ...]` to normalize `[x,y] ++ rest'` to `x :: y :: rest'`
- `simp [virtualPileTypes_length]` can fail on goals with `if matchesLiteral` (triggers internal `decide`); use targeted rewrites instead

## Overview

Prove `endTestWord_consumption` by splitting into 5 sub-lemmas,
each following the same pattern used for `testWord_consumption`:
decide gadget → lift → applyWord_append → shift.

## Sub-lemmas

### 1. `endTestWord_consumption_disq`
- **From**: CLAUSE_DISQ
- **Result**: ≥ nextBad = 2*m + applyWord suffix (vpt ALIGN rest) CHAIN_DISQ
- **Gadget** (decide): ∀ lp st nt1 nt2, applyWord (match lp ...) (vpt ALIGN [st, nt1, nt2]) CLAUSE_DISQ ≥ CHAIN_DISQ + 2*m
- **Lift**: gadget_lift_ge, A=[], window=[x,y,z], B=rest'
- **Shift**: 2-block shift past [x,y], suffix from CHAIN_DISQ on vpt ALIGN rest

### 2. `endTestWord_consumption_actd_good`
- **From**: ACTD, **when** y = Q
- **Result**: = nextGood = m + applyWord suffix (vpt ALIGN (y :: rest)) END_POS
- **Gadget** (decide): ∀ lp st nt2, applyWord (match lp ...) (vpt ALIGN [st, Q, nt2]) ACTD = END_POS + m
- **Lift**: gadget_lift_eq, A=[], window=[x,Q,z], B=rest'
- **Shift**: 1-block shift past [x], suffix from END_POS on vpt ALIGN (Q :: rest)

### 3. `endTestWord_consumption_actd_bad`
- **From**: ACTD, **when** y ≠ Q
- **Result**: ≥ nextBad
- **Gadget** (decide): ∀ lp st nt2, applyWord (match lp ...) (vpt ALIGN [st, S, nt2]) ACTD ≥ CHAIN_DISQ + 2*m
- **Lift**: gadget_lift_ge
- **Shift**: 2-block shift past [x,y], suffix from CHAIN_DISQ on vpt ALIGN rest

### 4. `endTestWord_consumption_nactd_good`
- **From**: NACTD, **when** y = Q **and** matchesLiteral x i clause
- **Result**: = nextGood
- **Gadget** (decide): ∀ lp st nt2, litMatches lp st → applyWord (match lp ...) (vpt ALIGN [st, Q, nt2]) NACTD = END_POS + m
- **Lift**: gadget_lift_eq
- **Shift**: 1-block shift past [x], suffix from END_POS on vpt ALIGN (Q :: rest)

### 5. `endTestWord_consumption_nactd_bad`
- **From**: NACTD, **when** y = Q **and** ¬matchesLiteral x i clause
- **Result**: ≥ nextBad
- **Gadget** (decide): ∀ lp st nt2, ¬litMatches lp st → applyWord (match lp ...) (vpt ALIGN [st, Q, nt2]) NACTD ≥ CHAIN_DISQ + 2*m
- **Lift**: gadget_lift_ge
- **Shift**: 2-block shift past [x,y], suffix from CHAIN_DISQ on vpt ALIGN rest

## Assembly

`endTestWord_consumption` assembles the 5 sub-lemmas:
- Part 1 (CLAUSE_DISQ): directly from sub-lemma 1.
- Part 2 (if y = Q then ...):
  - `if_pos rfl` branch:
    - ACTD = nextGood: sub-lemma 2
    - NACTD: `if matchesLiteral` splits to sub-lemma 4 (good) or 5 (bad)
  - `if_neg` branch:
    - ACTD ≥ nextBad: sub-lemma 3

## Common pattern (per sub-lemma)

1. **Gadget helper** proved by `decide` over LitPresence × PileType × PileType
   (using `litMatches` for the NACTD cases that need it)
2. **Decompose** rest = z :: rest'
3. **Specialize** gadget to endTestWord via `unfold endTestWord; exact gadget ...`
   (and `unfold matchesLiteral` for cases 4/5)
4. **Lift** to full machine via gadget_lift_eq/ge (A=[], window=[x,y,z], B=rest')
5. **Split** word ++ suffix via applyWord_append, substitute gadget result
6. **Shift** past consumed blocks via applyWord_compile_append_shift:
   - nextGood: A = vpt ALIGN [x], landing at END_POS in vpt ALIGN (y :: rest)
   - nextBad: A = vpt ALIGN [x, y], landing at CHAIN_DISQ in vpt ALIGN rest

## Notes

- The NACTD + y ≠ Q case is omitted from the theorem statement
  ("subsumed by ACTD since NACTD is closer to the end than ACTD").
  This means sub-lemma 3 (ACTD bad) covers it via monotonicity at the call site.
- The gadget window is [x, y, z] (3 elements) vs [x, y] (2 elements) for testWord.
  Bounds checks (s < vpt length, r < vpt length) change accordingly:
  vpt ALIGN [x,y,z] has length 3 * ALIGN.length = 18.
