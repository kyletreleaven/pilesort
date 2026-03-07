# PileSort — Lean 4 Formalization

Machine-checked proofs for the NP-hardness reduction gadgets from
"Sorting by pile shuffles on queue-like and stack-like piles can be hard"
([arXiv:2506.05518](https://arxiv.org/abs/2506.05518)).

The Python code in `setiptah-pilesort-hard` defines finite state automata
over pile types (Q=queue, S=stack), gadget words, and tests that verify
properties of these gadgets. Each test checks a finite set of cases and
becomes a machine-verified Lean 4 theorem proved by `decide` / `native_decide`.

## Prerequisites

Install [elan](https://github.com/leanprover/elan) (the Lean version manager):

```sh
curl https://elan.lean-lang.org/install.sh -sSf | sh
```

This project uses Lean 4.16.0, which elan will install automatically on first build.

## Building

```sh
cd setiptah-pilesort-lean
~/.elan/bin/lake build
```

A successful build verifies all proofs (any remaining `sorry` will produce warnings).

## Project Structure

```
setiptah-pilesort-lean/
  lakefile.lean
  lean-toolchain
  PileSort.lean              -- root import
  PileSort/
    Basic.lean               -- PileType, Action inductive types + Decidable instances
    Automata.lean            -- compile (direct step function), applyWord
    VirtualPileTypes.lean    -- virtualPileTypes and helpers
    Words.lean               -- gadget word constants + state position constants
    Mono.lean                -- monotonicity of applyWord for compiled machines
    Gadgets/
      StartClause.lean       -- theorem start_clause_correct
      Next.lean              -- theorem next_correct
      ForceQ.lean            -- theorem forceq_correct
      Activation.lean        -- theorem activation_correct
      EndActivation.lean     -- theorem end_activation_correct
      Alignment.lean         -- theorems align_aligned_correct + align_unaligned_correct
      Lifting.lean           -- gadget_lift_eq, gadget_lift_ge
    Reduction.lean           -- Literal, Clause, testWord, clauseWord, formulaWord, accepts
    TestConsume.lean         -- testWord and endTestWord consumption lemmas
    ClauseWord.lean          -- clauseWord_correct (composing gadget theorems)
    ClauseWordCorrect.lean   -- clauseWord_correct adapter lemmas for replicated types
    FormulaWord.lean         -- formulaWord_correct (composing clauseWord_correct)
```

## Type Representations

### PileType and Action (Basic.lean)

```lean
inductive PileType where | Q | S
  deriving DecidableEq, Repr, Inhabited

inductive Action where | a | d
  deriving DecidableEq, Repr, Inhabited
```

Both have custom `Decidable` instances for `∀`/`∃` quantifiers so that
`decide` can enumerate all values. (Avoids Mathlib's `Fintype` to keep
the project dependency-free.)

### compile (Automata.lean)

```lean
def compile (types : List PileType) (act : Action) (s : Nat) : Nat :=
  if h : s < types.length then
    match types[s], act with
    | .Q, .a => s
    | .Q, .d => s + 1
    | .S, .a => s + 1
    | .S, .d => s
  else s
```

Direct step function (replacing an earlier list-based `Machine`). Structural
proofs reduce to `unfold compile; split <;> omega`.

### applyWord

```lean
def applyWord (word : List Action) (step : Action → Nat → Nat) (s : Nat) : Nat :=
  word.foldl (fun s act => step act s) s
```

Generic over any step function. Gadget proofs use `applyWord word (compile types) s`.

### Key functions

| Python | Lean | Notes |
|--------|------|-------|
| `compile(pile_types)` | `compile : List PileType → Action → Nat → Nat` | Direct step function |
| `apply_word(machine, state, word)` | `applyWord : List Action → (Action → Nat → Nat) → Nat → Nat` | `List.foldl` over word |
| `virtual_pile_types(pt1, pt2)` | `virtualPileTypes : List PileType → List PileType → List PileType` | `pt2.flatMap (applyPile · pt1)` |

## Word Constants (Words.lean)

Short words (≤20 actions): explicit list literals like `[d, a, a, a, a, d, d, a]`.

Long words (ALIGNMENT_CODE, 162 actions): use a compile-time helper:

```lean
def toActions : List Char → List Action
  | [] => []
  | 'R' :: rest => .a :: toActions rest
  | _ :: rest => .d :: toActions rest
```

State position constants: `START_POS := 0`, `CHAIN_DISQ := 1`,
`ACTD := 2`, `NACTD := 3`, `END_POS := CLAUSE_DISQ := 5`.

## Proof Strategy

**`decide`** verifies by kernel reduction — fully trusted, no external
compiler dependency.

**`native_decide`** compiles the decision procedure to native code.
Faster but trusts the compiler. Used for the unaligned alignment check
(512 × 6 cases with 162-step evaluations — too slow for kernel reduction).

### Monotonicity (Mono.lean)

`applyWord_mono`: `compile` preserves ≤, proved by induction on the word
using two helpers proved by `unfold compile; split <;> omega`:
- `compile_step_ge`: `s ≤ compile types act s`
- `compile_step_le`: `compile types act s ≤ s + 1`

### Formula-level proof (FormulaWord.lean)

The proof is organized around `formulaState`, a tail-recursive computation
that mirrors the clause-by-clause structure of `formulaWord`. See the module
doc in `FormulaWord.lean` for the full strategy.

## Status

| Phase | Content | Status |
|-------|---------|--------|
| 1 | Core infrastructure + StartClause, Next, ForceQ | Done |
| 2 | Activation, EndActivation | Done |
| 3 | Alignment, Monotonicity, compile refactor | Done |
| 4 | SAT reduction: clauseWord_correct, formulaWord_correct | Done |

## Reference Files

| File | Role |
|------|------|
| `setiptah-pilesort-hard/src/setiptah/pilesort/hard/automata.py` | `compile`, `apply_word` |
| `setiptah-pilesort-hard/src/setiptah/pilesort/hard/words.py` | Word constants, state positions |
| `setiptah-pilesort-hard/test/test_words.py` | 7 tests → 7 theorems |
| `setiptah-pilesort/src/setiptah/pilesort/multiround.py` | `virtual_pile_types`, `apply_pile` |
