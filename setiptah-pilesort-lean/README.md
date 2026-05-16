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
theorem formulaWord_correct_multiSortable (n : Nat) (clauses : List Clause)
    (xs : List PileType) (hn : n ≥ 1) (hxs_len : xs.length = n + 1) (hne : clauses ≠ []) :
    MultiSortable (deckOfWord (formulaWord n clauses))
      [ALIGN, xs, List.replicate clauses.length PileType.Q] ↔
      HasMatchingAssignment n xs (satisfiesFormula · clauses)
```

in `PileSort/Reduction/SATToShuffle/SortableIff.lean`.

## Building up from the Python code
The Python code in `setiptah-pilesort-hard` defines finite state automata
over pile types (Q=queue, S=stack), gadget words, and tests that verify
properties of these gadgets.
Each test checks a finite set of cases exhaustively.

This project bridges the gap from those brute-force gadget checks to the
correctness of the full reduction:
Each gadget lemma becomes a machine-verified Lean 4 theorem proved by `decide` / `native_decide`.
Then they are composed by hand into `formulaWord_correct_multiSortable`.

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
PileSort.lean                        -- root import
PileSort/
  PileTypes.lean                     -- PileType inductive + Decidable instances
  Lists.lean                         -- general-purpose list lemmas
  Permutations.lean                  -- bijections of Fin n, Fin.invOf
  CatOrder.lean                      -- indexOf ordering in Nodup concatenations
  SAT/Defs.lean                      -- LitPresence, Clause, satisfiesFormula
  MatchingChain/
    Defs.lean                        -- Action, compile, applyWord, accepts
    Mono.lean                        -- monotonicity, sink, append decomposition
  Shuffle/
    Defs.lean                        -- Deck, dealToPile, shuffleRound, Sortable
    Properties.lean                  -- shuffleRound_order, shuffleRound_consecutive
    MultiRound/Defs.lean             -- ShuffleSpec, multiShuffleRound, MultiSortable
  Reduction/
    SATToShuffle/
      VarEncoding.lean               -- embedVar, embedVars, litMatches, HasMatchingAssignment
      VarEncodingLemmas.lean         -- encoding/satisfaction bridge lemmas
      SortableIff.lean               -- top-level theorems (formulaWord_correct_*)
    SATToMatchingChain/
      Defs/Words.lean                -- gadget word constants, state positions
      Defs/FormulaDefs.lean          -- testWord, clauseWord, formulaWord
      Gadgets/                       -- per-gadget correctness theorems
      TestConsume.lean               -- testWord consumption lemmas
      TestChain.lean                 -- consumption lemmas for testWord sequences
      ClauseWord.lean                -- clauseWord consumption
      FormulaWord.lean               -- formulaWord_correct
    ShuffleMultiRoundToSingle/
      VirtualPileTypes.lean          -- virtualPileTypes, applyPile, orient
      VirtualShuffles.lean           -- combinedSpec, shuffleRound_virtualPileTypes
      MultiRound.lean                -- multiSortable_iff_sortable
    ShuffleMatchingChain/
      SortableIff.lean               -- sortable_iff_accepts
      ChangeProfiles.lean            -- deckOfWord, changeProfile
```

## Proof Strategy

**`decide`** verifies by kernel reduction — fully trusted, no external
compiler dependency.

**`native_decide`** compiles the decision procedure to native code.
Faster but trusts the compiler. Used for the unaligned alignment check
(512 × 6 cases with 162-step evaluations — too slow for kernel reduction).

### Layered proof

`formulaWord_correct` is proved via a stack of *consumption-form* lemmas
(`TestChain.lean` → `ClauseWord.lean` → `FormulaWord.lean`).

<!-- TODO: explain consumption-form proof strategy more clearly -->
