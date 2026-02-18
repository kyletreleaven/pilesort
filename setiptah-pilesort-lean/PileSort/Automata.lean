/-
  Finite state automaton for pile shuffle sort.

  Mirrors automata.py:
    compile(pile_types) -> step function (Action → Nat → Nat)
    applyWord(word, step, state) -> final state

  For pile_types of length n, states range over {0, ..., n}.
  State n is the absorbing/sink state.

  The rule: action `a` stays at position k if pile k is Q (queue);
  action `d` stays at position k if pile k is S (stack);
  otherwise advance to k+1.
-/
import PileSort.Basic

/-- Compiled step function from a list of pile types.
    For state s < types.length, looks up types[s] and either stays or advances.
    For state s ≥ types.length (sink state), stays. -/
def compile (types : List PileType) (act : Action) (s : Nat) : Nat :=
  if h : s < types.length then
    match types[s], act with
    | .Q, .a => s
    | .Q, .d => s + 1
    | .S, .a => s + 1
    | .S, .d => s
  else s

/-- Apply a word (list of actions) using a step function starting from a given state.
    Mirrors apply_word in automata.py. -/
def applyWord (word : List Action) (step : Action → Nat → Nat) (s : Nat) : Nat :=
  word.foldl (fun s act => step act s) s
