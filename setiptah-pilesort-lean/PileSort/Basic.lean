/-
  Basic types for pile shuffle sort formalization.

  PileType: Queue (Q) or Stack (S)
  Action: advance (a, corresponds to R in paper) or descend (d, corresponds to L)
-/
import PileSort.PileTypes

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

theorem embedVars_surjective : ∀ (xs : List PileType),
    ∃ vars : List Bool, vars.length = xs.length ∧ embedVars vars = xs
  | [] => ⟨[], rfl, rfl⟩
  | x :: rest => by
    obtain ⟨vars, hlen, heq⟩ := embedVars_surjective rest
    refine ⟨(x = .Q) :: vars, by simp [hlen], ?_⟩
    unfold embedVars; simp only [List.map]; unfold embedVar
    cases x <;> simp [embedVars] at heq ⊢ <;> exact heq
