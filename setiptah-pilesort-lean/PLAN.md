# Lean 4 Formalization of Pile Shuffle Sort Hardness Proof

## Context

This project formalizes the computational complexity gadgets from
"Sorting by pile shuffles on queue-like and stack-like piles can be hard"
([arXiv:2506.05518](https://arxiv.org/abs/2506.05518)).

The Python code in `setiptah-pilesort-hard` defines finite state automata
over pile types (Q=queue, S=stack), gadget words, and tests that verify
properties of these gadgets. Each test checks a finite set of cases and
can be turned into a machine-verified proof in Lean 4 using `decide` /
`native_decide` (which verify decidable propositions by exhaustive computation).

## Project Structure

```
setiptah-pilesort-lean/
  lakefile.lean
  lean-toolchain
  PileSort.lean              -- root import
  PileSort/
    Basic.lean               -- PileType, Action inductive types + Fintype
    Automata.lean            -- Machine, compile, applyWord
    VirtualPileTypes.lean    -- virtualPileTypes and helpers
    Words.lean               -- gadget word constants + state position constants
    Gadgets/
      StartClause.lean       -- theorem start_clause_correct
      Next.lean              -- theorem next_correct
      ForceQ.lean            -- theorem forceq_correct
      Activation.lean        -- theorem activation_correct
      EndActivation.lean     -- theorem end_activation_correct
      Alignment.lean         -- theorems align_aligned + align_unaligned
```

## Type Representations

### PileType and Action (Basic.lean)

```lean
inductive PileType where | Q | S
  deriving DecidableEq, Repr, Inhabited

inductive Action where | a | d
  deriving DecidableEq, Repr, Inhabited
```

Both need `Fintype` instances so that `decide` can enumerate universal
quantifiers over them.

### Machine (Automata.lean)

```lean
structure Machine where
  on_a : List Nat    -- transition table for Action.a
  on_d : List Nat    -- transition table for Action.d
```

Transition tables are `List Nat` of length `n+1` where `n` is the number
of pile types. State `n` is the absorbing/sink state.

### Key functions

| Python | Lean | Notes |
|--------|------|-------|
| `compile(pile_types)` | `compile : List PileType → Machine` | Use structural recursion, not `List.enum` |
| `apply_word(machine, state, word)` | `applyWord : Machine → Nat → List Action → Nat` | `List.foldl` over word |
| `virtual_pile_types(pt1, pt2)` | `virtualPileTypes : List PileType → List PileType → List PileType` | `pt2.bind (applyPile · pt1)` |

### compile implementation detail

Avoid `List.enum`; use a recursive helper for reliable kernel reduction:

```lean
def compileAux (types : List PileType) (k n : Nat) : List Nat × List Nat :=
  match types with
  | [] => ([], [])
  | .Q :: rest => let (as_, ds_) := compileAux rest (k+1) n; (k :: as_, min (k+1) n :: ds_)
  | .S :: rest => let (as_, ds_) := compileAux rest (k+1) n; (min (k+1) n :: as_, k :: ds_)

def compile (types : List PileType) : Machine :=
  let n := types.length
  let (as_, ds_) := compileAux types 0 n
  { on_a := as_ ++ [n], on_d := ds_ ++ [n] }
```

### Machine.step

```lean
def Machine.step (m : Machine) (act : Action) (state : Nat) : Nat :=
  let table := match act with | .a => m.on_a | .d => m.on_d
  (table.get? state).getD (table.length - 1)
```

Using `get?` + `getD` avoids proof obligations and stays total.

## Word Constants (Words.lean)

Short words (≤20 actions): explicit list literals like `[d, a, a, a, a, d, d, a]`.

Long words (ALIGNMENT_CODE, 162 actions): use a compile-time helper:

```lean
def toActions : List Char → List Action
  | [] => []
  | 'R' :: rest => .a :: toActions rest
  | _ :: rest => .d :: toActions rest

def ALIGNMENT_CODE : List Action :=
  toActions "RRR...".toList   -- full 162-char string
```

State position constants: `START_POS := 0`, `CHAIN_DISQ := 1`,
`ACTD := 2`, `NACTD := 3`, `END_POS := CLAUSE_DISQ := 5`.

## Proof Strategy

Each Python test becomes a Lean theorem proved by `decide` or `native_decide`.

**`decide`** verifies by kernel reduction (pure, no trust issues).
**`native_decide`** compiles to native code (fast, trusts the compiler).

Use `decide` where feasible; fall back to `native_decide` for large
computations (especially ALIGNMENT_CODE with its 162-step evaluations
over hundreds of configurations).

### Lemma patterns

**Finite enumeration**: For `∀ (t : PileType), P t`, `decide` checks
both `P .Q` and `P .S`. Similarly `∀ (i : Fin 3), P i` checks 3 cases.

**Conjunctions of concrete equalities/inequalities**: Each gadget lemma
reduces to a conjunction like `applyWord (compile ...) k w = v ∧ ...`
which is decidable via `Nat.decEq` and `Nat.decLe`.

### Example: start_clause_correct

```lean
theorem start_clause_correct :
    (applyWord (compile (virtualPileTypes ALIGN [.Q])) START_POS START_CLAUSE = NACTD) ∧
    (applyWord (compile (virtualPileTypes ALIGN [.Q])) CHAIN_DISQ START_CLAUSE ≥ CLAUSE_DISQ) ∧
    (applyWord (compile (virtualPileTypes ALIGN [.S])) START_POS START_CLAUSE = NACTD) ∧
    (applyWord (compile (virtualPileTypes ALIGN [.S])) CHAIN_DISQ START_CLAUSE ≥ CLAUSE_DISQ)
  := by native_decide
```

### Example: activation using quantifiers

```lean
def activationProp (word : List Action) (st nt : PileType) (sp : Nat) : Prop :=
  let m := compile (virtualPileTypes ALIGN [st, nt])
  let ep := applyWord m sp word
  let n := ALIGN.length
  if sp = CLAUSE_DISQ then ep ≥ CLAUSE_DISQ + n
  else if sp = ACTD ∨ (word = POS ∧ st = .Q) ∨ (word = NEG ∧ st = .S)
  then ep = ACTD + n
  else ep = NACTD + n

theorem activation_correct :
    (∀ st nt : PileType, ∀ sp : Fin 3,
      activationProp POS st nt ([NACTD, ACTD, CLAUSE_DISQ].get sp)) ∧
    (∀ st nt : PileType, ∀ sp : Fin 3,
      activationProp NEG st nt ([NACTD, ACTD, CLAUSE_DISQ].get sp)) ∧
    (∀ st nt : PileType, ∀ sp : Fin 3,
      activationProp DK st nt ([NACTD, ACTD, CLAUSE_DISQ].get sp))
  := by native_decide
```

### Alignment (hardest case)

- **Aligned**: `∀ types2 : Fin 8, ...` (8 = 2^3 configurations of 3 types)
  checks that `"QS..."` prefix → exact position, otherwise penalty.
- **Unaligned**: enumerate all 2^9 = 512 nine-char pile type strings,
  filter to ~224 distinct non-aligned virtual pile types, check penalty
  for each starting position 0..5. Use `native_decide`.

## Implementation Phases

### Phase 1 (first iteration) — Core + 3 simple gadgets
1. Set up Lean project (`lake init`, `lakefile.lean`, `lean-toolchain`)
2. `Basic.lean` — types with `DecidableEq`, `Fintype`
3. `Automata.lean` — `Machine`, `compile`, `applyWord`
4. `VirtualPileTypes.lean` — `virtualPileTypes` and helpers
5. `Words.lean` — all constants
6. Smoke test: `#eval applyWord (compile (virtualPileTypes ALIGN [.Q])) 0 START_CLAUSE`
   → should return `3` (= NACTD)
7. `Gadgets/StartClause.lean` — prove `start_clause_correct`
8. `Gadgets/Next.lean` — prove `next_correct` (2 cases)
9. `Gadgets/ForceQ.lean` — prove `forceq_correct` (8 cases)

### Phase 2 — Activation gadgets
10. `Gadgets/Activation.lean` — prove `activation_correct` (36 cases)
11. `Gadgets/EndActivation.lean` — prove `end_activation_correct` (72 cases)

### Phase 3 — Alignment gadgets
12. `Gadgets/Alignment.lean` — prove `align_aligned_correct` + `align_unaligned_correct`
    (~1360 cases, `native_decide`)

### Phase 4+ — Full reduction proof
Higher-level composition of gadgets into the NP-hardness reduction
(clause chains, round structure, cost analysis). To be designed after
Phase 3 is complete.

## Verification

After each phase, run `lake build` to verify all proofs type-check.
Cross-reference with `pytest` results from the Python test suite.

## Reference Files

| File | Role |
|------|------|
| `setiptah-pilesort-hard/src/setiptah/pilesort/hard/automata.py` | `compile`, `apply_word` |
| `setiptah-pilesort-hard/src/setiptah/pilesort/hard/words.py` | Word constants, state positions |
| `setiptah-pilesort-hard/test/test_words.py` | 7 tests → 7 theorems |
| `setiptah-pilesort/src/setiptah/pilesort/multiround.py` | `virtual_pile_types`, `apply_pile`, `apply_stack` |
| `setiptah-pilesort-hard/src/setiptah/pilesort/hard/util.py` | `powerspace` (enumeration helper) |
