import PileSort.PileTypes
import PileSort.SAT.Defs

/-- Encode a Boolean variable value as a pile type. -/
def embedVar : Bool → PileType
  | true  => .Q
  | false => .S

/-- Encode a Boolean assignment as a list of pile types. -/
def embedVars (vars : List Bool) : List PileType :=
  vars.map embedVar

theorem embedVars_injective : ∀ (a b : List Bool), embedVars a = embedVars b → a = b
  | [], [], _ => rfl
  | [], _::_, h => by simp [embedVars, List.map] at h
  | _::_, [], h => by simp [embedVars, List.map] at h
  | x::xs, y::ys, h => by
    simp [embedVars, List.map] at h
    have hxy : x = y := by cases x <;> cases y <;> simp_all [embedVar]
    subst hxy
    exact congrArg (x :: ·) (embedVars_injective xs ys h.2)

def litMatches (lp : LitPresence) (x : PileType) : Prop :=
  (lp = .pos ∧ x = .Q) ∨ (lp = .neg ∧ x = .S)

instance (lp : LitPresence) (x : PileType) : Decidable (litMatches lp x) := by
  unfold litMatches; infer_instance

def matchesLiteral (x : PileType) (i : Nat) (clause : Clause) : Prop :=
  litMatches (clause.getD i .absent) x

instance (x : PileType) (i : Nat) (clause : Clause) : Decidable (matchesLiteral x i clause) := by
  unfold matchesLiteral; infer_instance

theorem matchesLiteral_eq_litMatches (x : PileType) (i : Nat) (clause : Clause) :
    matchesLiteral x i clause = litMatches (clause.getD i .absent) x := rfl

theorem embedVars_surjective : ∀ (xs : List PileType),
    ∃ vars : List Bool, vars.length = xs.length ∧ embedVars vars = xs
  | [] => ⟨[], rfl, rfl⟩
  | x :: rest => by
    obtain ⟨vars, hlen, heq⟩ := embedVars_surjective rest
    refine ⟨(x = .Q) :: vars, by simp [hlen], ?_⟩
    unfold embedVars
    simp only [List.map]
    unfold embedVar
    cases x <;> simp [embedVars] at heq ⊢ <;> exact heq
