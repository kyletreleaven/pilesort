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

/-- When s < n, compiled step returns s or s+1: upper bound. -/
theorem compile_step_le (types : List PileType) (act : Action) (s : Nat)
    (h : s < types.length) :
    (compile types).step act s ≤ s + 1 := by
  sorry

/-- When s < n, compiled step returns s or s+1: lower bound. -/
theorem compile_step_ge (types : List PileType) (act : Action) (s : Nat)
    (h : s < types.length) :
    s ≤ (compile types).step act s := by
  sorry

/-- When s ≥ n, compiled step returns n (the sink). -/
theorem compile_step_sink (types : List PileType) (act : Action) (s : Nat)
    (h : types.length ≤ s) :
    (compile types).step act s = types.length := by
  sorry

/-- compile always produces monotone machines. -/
theorem compile_monotone (types : List PileType) : (compile types).Monotone := by
  intro act s₁ s₂ hs
  by_cases heq : s₁ = s₂
  · subst heq; exact Nat.le_refl _
  · -- s₁ < s₂
    have hlt : s₁ + 1 ≤ s₂ := by omega
    by_cases h₁ : s₁ < types.length
    · -- s₁ in bounds
      by_cases h₂ : s₂ < types.length
      · -- both in bounds: step s₁ ≤ s₁+1 ≤ s₂ ≤ step s₂
        calc (compile types).step act s₁
            _ ≤ s₁ + 1 := compile_step_le types act s₁ h₁
            _ ≤ s₂ := hlt
            _ ≤ (compile types).step act s₂ := compile_step_ge types act s₂ h₂
      · -- s₁ in bounds, s₂ out: step s₁ ≤ s₁+1 ≤ n = step s₂
        calc (compile types).step act s₁
            _ ≤ s₁ + 1 := compile_step_le types act s₁ h₁
            _ ≤ types.length := by omega
            _ = (compile types).step act s₂ := (compile_step_sink types act s₂ (by omega)).symm
    · -- s₁ out of bounds, so s₂ out too: both map to n
      simp [compile_step_sink types act s₁ (by omega),
            compile_step_sink types act s₂ (by omega)]
