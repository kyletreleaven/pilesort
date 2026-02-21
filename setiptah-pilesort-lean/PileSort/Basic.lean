/-
  Basic types for pile shuffle sort formalization.

  PileType: Queue (Q) or Stack (S)
  Action: advance (a, corresponds to R in paper) or descend (d, corresponds to L)
-/

inductive PileType where
  | Q : PileType
  | S : PileType
  deriving DecidableEq, Repr, Inhabited

inductive Action where
  | a : Action
  | d : Action
  deriving DecidableEq, Repr, Inhabited

def embedVar : Bool → PileType
  | true  => .Q
  | false => .S

def embedVars (vars : List Bool) : List PileType :=
  vars.map embedVar

theorem embedVars_injective : ∀ (a b : List Bool), embedVars a = embedVars b → a = b
  | [], [], _ => rfl
  | [], _::_, h => by simp [embedVars, List.map] at h
  | _::_, [], h => by simp [embedVars, List.map] at h
  | x::xs, y::ys, h => by
    simp [embedVars, List.map] at h
    have hxy : x = y := by cases x <;> cases y <;> simp_all [embedVar]
    subst hxy; exact congrArg (x :: ·) (embedVars_injective xs ys h.2)

-- Decidable instances for universal/existential quantifiers over PileType.
-- This avoids depending on Mathlib's Fintype.

instance {p : PileType → Prop} [Decidable (p .Q)] [Decidable (p .S)] :
    Decidable (∀ x : PileType, p x) :=
  if hQ : p .Q then
    if hS : p .S then
      isTrue (fun x => by cases x <;> assumption)
    else
      isFalse (fun h => hS (h .S))
  else
    isFalse (fun h => hQ (h .Q))

instance {p : PileType → Prop} [Decidable (p .Q)] [Decidable (p .S)] :
    Decidable (∃ x : PileType, p x) :=
  if hQ : p .Q then
    isTrue ⟨.Q, hQ⟩
  else if hS : p .S then
    isTrue ⟨.S, hS⟩
  else
    isFalse (fun ⟨x, hx⟩ => by cases x <;> contradiction)
