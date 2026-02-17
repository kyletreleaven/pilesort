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
