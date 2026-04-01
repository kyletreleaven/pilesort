/-!
  Shared alphabets for the pile-sort formalization.

  `PileType` is the Q/S alphabet used by both the shuffle and matching-chain
  problems.
-/

inductive PileType where
  | Q : PileType
  | S : PileType
  deriving DecidableEq, Repr, Inhabited

-- Decidable instances for universal/existential quantifiers over `PileType`.
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
