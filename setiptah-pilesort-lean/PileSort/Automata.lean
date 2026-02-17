/-
  Finite state automaton for pile shuffle sort.

  Mirrors automata.py:
    compile(pile_types) -> machine with transition tables on_a, on_d
    apply_word(machine, state, word) -> final state
-/
import PileSort.Basic

/-- A compiled pile-shuffle automaton with transition tables for each action. -/
structure Machine where
  on_a : List Nat
  on_d : List Nat
  deriving DecidableEq, Repr

/-- Look up the next state for a given action.
    Uses List.get? with a default to stay total without proof obligations. -/
def Machine.step (m : Machine) (act : Action) (state : Nat) : Nat :=
  let table := match act with
    | .a => m.on_a
    | .d => m.on_d
  (table.get? state).getD (table.length - 1)

/-- Build transition tables from a list of pile types.

    For pile_types of length n, each table has length n+1.
    State n is the absorbing/sink state.

    The rule: action `a` stays at position k if pile k is Q (queue);
    action `d` stays at position k if pile k is S (stack);
    otherwise advance to min(k+1, n). -/
def compileAux (types : List PileType) (k n : Nat) : List Nat × List Nat :=
  match types with
  | [] => ([], [])
  | typ :: rest =>
    let (as_tail, ds_tail) := compileAux rest (k + 1) n
    match typ with
    | .Q => (k :: as_tail, min (k + 1) n :: ds_tail)
    | .S => (min (k + 1) n :: as_tail, k :: ds_tail)

def compile (types : List PileType) : Machine :=
  let n := types.length
  let (as_, ds_) := compileAux types 0 n
  { on_a := as_ ++ [n], on_d := ds_ ++ [n] }

/-- Apply a word (list of actions) to a machine starting from a given state.
    Mirrors apply_word in automata.py. -/
def applyWord (word : List Action) (m : Machine) (state : Nat) : Nat :=
  word.foldl (fun s act => m.step act s) state
