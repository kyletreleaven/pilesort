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

-- Fintype instances so `decide` can enumerate universal quantifiers

instance : Fintype PileType where
  elems := ⟨[.Q, .S], by simp⟩
  complete := fun x => by cases x <;> simp

instance : Fintype Action where
  elems := ⟨[.a, .d], by simp⟩
  complete := fun x => by cases x <;> simp
