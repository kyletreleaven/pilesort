import PileSort.PileTypes

/-!
  Finite state automaton for the matching-chain problem.

  Mirrors automata.py:
    compile(pile_types) -> step function (Action → Nat → Nat)
    applyWord(word, step, state) -> final state

  For pile_types of length n, states range over {0, ..., n}.
  State n is the absorbing/sink state.

  The rule: action `a` stays at position k if pile k is Q (queue);
  action `d` stays at position k if pile k is S (stack);
  otherwise advance to k+1.
-/

inductive Action where
  | a : Action
  | d : Action
  deriving DecidableEq, Repr, Inhabited

/-- Compiled step function from a list of pile types.
    For state `s < types.length`, looks up `types[s]` and either stays or
    advances. For `s ≥ types.length` (the sink state), it stays put. -/
def compile (types : List PileType) (act : Action) (s : Nat) : Nat :=
  if h : s < types.length then
    match types[s], act with
    | .Q, .a => s
    | .Q, .d => s + 1
    | .S, .a => s + 1
    | .S, .d => s
  else s

/-- Apply a word using a step function from a given starting state. -/
def applyWord (word : List Action) (step : Action → Nat → Nat) (s : Nat) : Nat :=
  word.foldl (fun s act => step act s) s

/-- A compiled matching-chain instance accepts a word if starting from state `0`
    it avoids the sink state `types.length`. -/
def accepts (types : List PileType) (word : List Action) : Prop :=
  applyWord word (compile types) 0 < types.length
