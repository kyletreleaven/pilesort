# PileSort — Lean 4 Formalization

Machine-checked proofs for the NP-hardness reduction from
"Sorting by pile shuffles on queue-like and stack-like piles can be hard"
([arXiv:2506.05518](https://arxiv.org/abs/2506.05518)).

## Introduction

In pile shuffle, a deck of cards is repeatedly *dealt* into piles and
*collected* back. Each pile is either queue-like (Q: dealt face-up) or stack-like (S: dealt face-down). A
permutation is sortable if there exists a type assignment
for each pile in each round
so that some deal can return the deck in sorted order. The paper shows that deciding sortability
is NP-hard in certain scenarios when pile types can be heterogeneous (mixed Q and S across piles).

## Proof by Reduction

The main theorem of this project reduces SAT to an abstraction of pile-sort feasibility via a word construction:
given a CNF formula with `n` variables and `m` clauses, `formulaWord n clauses`
is a sequence of "actions" such that a specific automaton accepts it if and
only if the formula is satisfiable. 
The word itself is an abstract representation of the input permutation,
while the candidate automata correspond to the allowable pile-type assignments for a shuffle.

The top-level Lean theorem is:

```lean
theorem formulaWord_correct (n : Nat) (clauses : List Clause)
    (xs : List PileType) (hn : n ≥ 1) (hxs_len : xs.length = n + 1) (hne : clauses ≠ []) :
    accepts
      (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate clauses.length PileType.Q))
      (formulaWord n clauses)
    ↔ HasMatchingAssignment n xs (satisfiesFormula · clauses)
```

where `accepts types word` holds when the compiled automaton for `types` does not
reach its sink state after processing `word` from state 0.


## Building up from the Python code
The Python code in `setiptah-pilesort-hard` defines finite state automata
over pile types (Q=queue, S=stack), gadget words, and tests that verify
properties of these gadgets.
Each test checks a finite set of cases exhaustively.

This project bridges the gap from those brute-force gadget checks to the
correctness of the full reduction:
Each gadget lemma becomes a machine-verified Lean 4 theorem proved by `decide` / `native_decide`.
Then they are composed by hand into `formulaWord_correct`.

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
      Alignment.lean         -- theorems align_aligned_correct + align_unaligned_correct
      Lifting.lean           -- gadget_lift_eq, gadget_lift_ge
    Reduction.lean           -- Literal, Clause, testWord, clauseWord, formulaWord, accepts
    TestConsume.lean         -- testWord and endTestWord consumption lemmas
    TestChain.lean           -- consumption-form lemmas for sequences of testWords
    ClauseWord.lean          -- legacy index-form testChain lemmas (not on main proof path)
    ClauseWordNew.lean       -- clauseWord_chain_consumption + HasMatchingAssignment theorems
    FormulaWordNew.lean      -- clauseNext_*_consumption + formulaWord_chain_pos'
    FormulaWord.lean         -- formulaWord_correct (composing clauseWord theorems)
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

### Formula-level proof

`formulaWord_correct` is proved via a stack of *consumption-form* lemmas.
The consumption form factors the behavior of a word sequence into a fixed
offset plus the behavior of a suffix on a residual machine:

```
applyWord (word ++ suffix) machine state = offset + applyWord suffix machine' state'
```

This makes lemmas composable: each layer hands the suffix down to the next.
The stack, bottom to top:

- **TestChain.lean** — consumption lemmas for sequences of `testWord`s in the
  plain-chain and end-capped cases.
- **ClauseWordNew.lean** — `clauseWord_chain_consumption` and the sat/nonsat
  consumption lemmas, plus bridge lemmas between the `HasMatchingAssignment`
  vocabulary and the raw `matchesLiteral` pile-type layer.
- **FormulaWordNew.lean** — `clauseNext_good_consumption`,
  `clauseNext_bad_consumption`, and `clauseNext_chain_consumption`, which lift
  one `clauseWord ++ NEXT` step to the replicated-types machine.
- **FormulaWord.lean** — `formulaWord_correct` by induction on clauses, using
  the three `clauseNext_*_consumption` lemmas as the inductive engine.

## Status

| Phase | Content | Status |
|-------|---------|--------|
| 1 | Core infrastructure + StartClause, Next, ForceQ | Done |
| 2 | Activation | Done |
| 3 | Alignment, Monotonicity, compile refactor | Done |
| 4 | SAT reduction: clauseWord_correct, formulaWord_correct | Done |

## Reference Files

| File | Role |
|------|------|
| `setiptah-pilesort-hard/src/setiptah/pilesort/hard/automata.py` | `compile`, `apply_word` |
| `setiptah-pilesort-hard/src/setiptah/pilesort/hard/words.py` | Word constants, state positions |
| `setiptah-pilesort-hard/test/test_words.py` | 7 tests → 7 theorems |
| `setiptah-pilesort/src/setiptah/pilesort/multiround.py` | `virtual_pile_types`, `apply_pile` |
