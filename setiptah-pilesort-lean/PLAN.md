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
```

## Type Representations

### PileType and Action (Basic.lean)

```lean
inductive PileType where | Q | S
  deriving DecidableEq, Repr, Inhabited

inductive Action where | a | d
  deriving DecidableEq, Repr, Inhabited
```

Both need custom `Decidable` instances for `∀`/`∃` quantifiers so that
`decide` can enumerate all values. (We avoid Mathlib's `Fintype` to keep
the project dependency-free.)

### compile (Automata.lean)

`compile` is a direct step function (no intermediate `Machine` structure):

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

This direct representation (replacing the earlier list-based `Machine`)
makes structural proofs trivial — properties like monotonicity reduce
to `unfold compile; split <;> omega`.

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

def ALIGNMENT_CODE : List Action :=
  toActions "RRR...".toList   -- full 162-char string
```

State position constants: `START_POS := 0`, `CHAIN_DISQ := 1`,
`ACTD := 2`, `NACTD := 3`, `END_POS := CLAUSE_DISQ := 5`.

## Proof Strategy

Each Python test becomes a Lean theorem proved by `decide`.

**`decide`** verifies by kernel reduction — fully trusted, no external
compiler dependency.

**`native_decide`** compiles the decision procedure to native code.
Faster but trusts the compiler. Used for the unaligned alignment check
(512 × 6 cases with 162-step evaluations — too slow for kernel reduction).

### Lemma patterns

**Finite enumeration**: For `∀ (t : PileType), P t`, `decide` checks
both `P .Q` and `P .S`. Similarly `∀ (i : Fin 3), P i` checks 3 cases.

**Conjunctions of concrete equalities/inequalities**: Each gadget lemma
reduces to a conjunction like `applyWord (compile ...) k w = v ∧ ...`
which is decidable via `Nat.decEq` and `Nat.decLe`.

**Bool-valued checks**: For large case checks (alignment unaligned),
define a `Bool` function that mirrors the Python test loop directly,
then prove `checkFoo = true` by `native_decide`. Avoids `Decidable`
synthesis issues with many quantifiers.

### Monotonicity (Mono.lean)

Structural proof (not decidable) that `compile` preserves ≤:

```lean
theorem applyWord_mono (word : List Action) (types : List PileType)
    {s₁ s₂ : Nat} (hs : s₁ ≤ s₂) :
    applyWord word (compile types) s₁ ≤ applyWord word (compile types) s₂
```

Proved by induction on `word`, using two helper lemmas about `compile`:
- `compile_step_ge`: `s ≤ compile types act s` (never goes backward)
- `compile_step_le`: `compile types act s ≤ s + 1` (advances by at most 1)

Both proved by `unfold compile; split; split <;> omega`. No boundedness
hypotheses needed — these hold for all `s`, not just `s ≤ types.length`.

## Implementation Phases

### Phase 1 — Core + 3 simple gadgets ✅ DONE
1. ✅ Set up Lean project (`lakefile.lean`, `lean-toolchain`)
2. ✅ `Basic.lean` — types with `DecidableEq`, custom `Decidable` instances
3. ✅ `Automata.lean` — `compile`, `applyWord`
4. ✅ `VirtualPileTypes.lean` — `virtualPileTypes` and helpers
5. ✅ `Words.lean` — all constants
6. ✅ `Gadgets/StartClause.lean` — prove `start_clause_correct`
7. ✅ `Gadgets/Next.lean` — prove `next_correct` (2 cases)
8. ✅ `Gadgets/ForceQ.lean` — prove `forceq_correct` (8 cases, all next_types)
9. ✅ `lake build` passes — all proofs verified by kernel reduction (`decide`)

### Phase 2 — Activation gadgets ✅ DONE
10. ✅ `Gadgets/Activation.lean` — prove `activation_correct` (36 cases, `decide`)
11. ✅ `Gadgets/EndActivation.lean` — prove `end_activation_correct` (72 cases, `decide`)
12. ✅ `lake build` passes

### Phase 3 — Alignment gadgets + Monotonicity ✅ DONE
13. ✅ `Gadgets/Alignment.lean` — `align_aligned_correct` (`decide`) + `align_unaligned_correct` (`native_decide`)
14. ✅ `Mono.lean` — `applyWord_mono` and helper lemmas (structural proofs)
15. ✅ Refactored `compile` from list-based `Machine` to direct step function
16. ✅ `lake build` passes — all 7 Python tests formalized as verified theorems

**Resolved issues during Phases 1–3**:
- `Fintype` is Mathlib-only; replaced with custom `Decidable` instances for `∀`/`∃` over `PileType`
- `List.bind` deprecated in Lean 4.16; replaced with `List.flatMap`
- `open Action in` only scopes to one definition; changed to section-level `open Action`
- List-based `Machine` made structural proofs hard; replaced with direct step function
- Alignment unaligned: too many quantifiers for `Decidable` synthesis; used `Bool` check + `native_decide`
- Alignment unaligned: `decide` too slow for 3072 × 162-step evaluations; `native_decide` handles it

### Phase 4 — SAT reduction proof (IN PROGRESS)

Compose the gadget theorems into the full NP-hardness reduction.

#### Current state
- `Reduction.lean` defines `Literal`, `Clause`, `testWord`, `endTestWord`,
  `clauseWord`, `formulaWord`, `satisfiesClause`, `satisfiesFormula`, `accepts`.
- `clauseWord_correct` and `formulaWord_correct` are stated with `sorry`.
- `next_correct` generalized to arbitrary position `k` in a virtualPileTypes list.
- `Mono.lean` has `applyWord_mono`, `applyWord_ge`, `applyWord_append_truncate`,
  `compile_append_left`, `compile_append_right`, `compile_sink`, `applyWord_sink`.

#### Helper lemmas needed

1. **`applyWord_append`**:
   `applyWord (w₁ ++ w₂) step s = applyWord w₂ step (applyWord w₁ step s)`
   — decompose word application over concatenation. Follows from `List.foldl_append`.

2. **`virtualPileTypes_append`**:
   `virtualPileTypes pt1 (A ++ B) = virtualPileTypes pt1 A ++ virtualPileTypes pt1 B`
   — follows from `List.flatMap_append`. Lets us view `virtualPileTypes inner (Q^m)`
   as `m` copies of `inner` concatenated, and decompose the type list into
   clause-sized blocks for applying `clauseWord_correct`.

#### Strategy for `formulaWord_correct`

**Theorem statement.** Given `xs : List PileType`, let
`types = virtualPileTypes (virtualPileTypes ALIGN xs) (Q^m)` where `m = clauses.length`.
Then `accepts types (formulaWord n clauses)` iff there exist `vars : List Bool`
with `vars.length = n`, `xs = embedVars vars ++ [Q]`, and `satisfiesFormula vars clauses`.

The ALIGN structure is assumed (not deduced from acceptance). The outer
`virtualPileTypes ... (Q^m)` replicates the inner pattern `m` times
(since `applyPile Q = id`). So `types` is `inner` repeated `m` times where
`inner = virtualPileTypes ALIGN xs`.

The formula word for clauses [φ₀, ..., φ_{m-1}] is:
```
clauseWord(φ₀) ++ NEXT ++ clauseWord(φ₁) ++ NEXT ++ ... ++ clauseWord(φ_{m-1})
```
(the `dropLast` removes the trailing NEXT).

By `virtualPileTypes_append`, `types` can also be viewed as
`virtualPileTypes ALIGN (xs^m)`, which is `virtualPileTypes ALIGN (A0 ++ A1 ++ A2)`
with the right decomposition for each clause's application of `clauseWord_correct`.

Let `block = n + 1` (length of `embedVars vars ++ [Q]`) and `m_a = ALIGN.length = 6`.

**Forward direction (⇐): satisfying assignment → accepts.**

Given `xs = embedVars vars ++ [Q]` and `satisfiesFormula vars clauses`.

Induction on clauses. Invariant: after processing clauses 0..j-1 and their
NEXTs, the state is `START_POS + j * block * m_a`.

At each clause j:
- `clauseWord_correct` (satisfied case, with A0 = first j copies of xs,
  A1 = j-th copy = embedVars vars ++ [Q], A2 = remaining copies):
  `START_POS + j*block*m_a → END_POS + (j*block + n)*m_a`
- `next_correct` (with k = j*block + n in the ALIGN-level virtual type list):
  `END_POS + (j*block+n)*m_a → START_POS + (j+1)*block*m_a`

For the last clause (j = m-1), there is no NEXT (it was `dropLast`-ed), so we
stop at `END_POS + (m*block - 1)*m_a`, which is `< m*block*m_a = types.length`.
Hence `accepts` holds.

**Backward direction (⇒): accepts → xs encodes a satisfying assignment.**

Two parts:

Contrapositive: if there is no satisfying `vars` such that
`xs = embedVars vars ++ [Q]`, then some clause has no matching satisfying
assignment. `clauseWord_correct` part 2 (reformulated) says: if there is no
`vars` with `A1 = embedVars vars ++ [Q]` AND `satisfiesClause vars clause`,
then the clause word sends the state to `≥ CHAIN_DISQ + (k+n+1)*m_a`.
This covers both "wrong xs structure" and "right structure but unsatisfied"
in one shot — no need for separate low-level gadget reasoning at the
formula level.

Once the state reaches a CHAIN_DISQ position:
- `clauseWord_correct` part 3: penalty propagates through subsequent clauses
  unconditionally.
- By `applyWord_mono` and `applyWord_ge`, the state never comes back down,
  eventually reaching `≥ types.length` — contradicting `accepts`.

#### Proof order
1. Prove `applyWord_append` and `virtualPileTypes_append` (small lemmas).
2. Prove `clauseWord_correct` (composing gadget theorems).
3. Prove forward direction of `formulaWord_correct` (induction on clauses).
4. Prove backward direction of `formulaWord_correct` (contrapositive + monotonicity).

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
