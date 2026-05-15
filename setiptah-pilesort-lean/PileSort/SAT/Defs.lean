/-!
  SAT definitions.

  A formula in CNF is represented as a `List Clause`.  Each `Clause` records,
  for each variable index, whether the positive literal, negative literal, or
  neither appears in that clause.
-/

inductive LitPresence where
  | pos : LitPresence
  | neg : LitPresence
  | absent : LitPresence
  deriving DecidableEq, Repr

instance {p : LitPresence → Prop}
    [Decidable (p .pos)] [Decidable (p .neg)] [Decidable (p .absent)] :
    Decidable (∀ x : LitPresence, p x) :=
  if hp : p .pos then
    if hn : p .neg then
      if ha : p .absent then
        isTrue (fun x => by cases x <;> assumption)
      else isFalse (fun h => ha (h .absent))
    else isFalse (fun h => hn (h .neg))
  else isFalse (fun h => hp (h .pos))

/-- A clause records, for each variable index, whether the positive literal,
    negative literal, or neither occurs. -/
abbrev Clause := List LitPresence

/-- A clause is satisfied by a variable assignment if some in-range literal matches.
    Out-of-range indices are inert. -/
def satisfiesClause (vars : List Bool) (clause : Clause) : Prop :=
  ∃ i, i < vars.length ∧
    ((clause.getD i .absent = .pos ∧ vars.getD i false = true) ∨
     (clause.getD i .absent = .neg ∧ vars.getD i false = false))

/-- A formula, represented as a list of clauses, is satisfied if every clause is
    satisfied. -/
def satisfiesFormula (vars : List Bool) (clauses : List Clause) : Prop :=
  ∀ clause ∈ clauses, satisfiesClause vars clause
