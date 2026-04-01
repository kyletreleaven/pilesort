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
import PileSort.MatchingChain
