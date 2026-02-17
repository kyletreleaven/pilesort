/-
  Monotonicity of applyWord for compiled machines.

  Key result: if s₁ ≤ s₂ then applyWord word (compile types) s₁ ≤ applyWord word (compile types) s₂
-/
import PileSort.Automata
import PileSort.Basic

/-- A machine is monotone if its step function preserves ≤. -/
def Machine.Monotone (m : Machine) : Prop :=
  ∀ (act : Action) (s₁ s₂ : Nat), s₁ ≤ s₂ → m.step act s₁ ≤ m.step act s₂

/-- applyWord preserves ≤ for monotone machines. -/
theorem applyWord_mono (word : List Action) {m : Machine} (hm : m.Monotone)
    {s₁ s₂ : Nat} (hs : s₁ ≤ s₂) :
    applyWord word m s₁ ≤ applyWord word m s₂ := by
  sorry

/-- compile always produces monotone machines. -/
theorem compile_monotone (types : List PileType) : (compile types).Monotone := by
  sorry
