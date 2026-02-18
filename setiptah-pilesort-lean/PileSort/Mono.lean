/-
  Monotonicity of applyWord for compiled machines.

  Key result: for s₁ ≤ s₂,
    applyWord word (compile types) s₁ ≤ applyWord word (compile types) s₂

  Proof strategy:
    Two facts about compiled step:
      1. s ≤ step act s         (step never goes backward)
      2. step act s ≤ s + 1     (step advances by at most 1)
    From s₁ < s₂: step s₁ ≤ s₁ + 1 ≤ s₂ ≤ step s₂
-/
import PileSort.Automata
import PileSort.Basic

/-- Compiled step never goes backward. -/
theorem compile_step_ge (types : List PileType) (act : Action) (s : Nat) :
    s ≤ compile types act s := by
  unfold compile
  split
  · split <;> omega
  · omega

/-- Compiled step advances by at most 1. -/
theorem compile_step_le (types : List PileType) (act : Action) (s : Nat) :
    compile types act s ≤ s + 1 := by
  unfold compile
  split
  · split <;> omega
  · omega

/-- Compiled step preserves ≤. -/
theorem compile_step_mono (types : List PileType) (act : Action) (s₁ s₂ : Nat)
    (hs : s₁ ≤ s₂) :
    compile types act s₁ ≤ compile types act s₂ := by
  by_cases heq : s₁ = s₂
  · subst heq; exact Nat.le_refl _
  · calc compile types act s₁
        _ ≤ s₁ + 1 := compile_step_le types act s₁
        _ ≤ s₂ := by omega
        _ ≤ compile types act s₂ := compile_step_ge types act s₂

/-- applyWord preserves ≤ for compiled machines. -/
theorem applyWord_mono (word : List Action) (types : List PileType)
    {s₁ s₂ : Nat} (hs : s₁ ≤ s₂) :
    applyWord word (compile types) s₁ ≤ applyWord word (compile types) s₂ := by
  revert s₁ s₂
  induction word with
  | nil =>
    intro s₁ s₂ hs
    exact hs
  | cons act rest ih =>
    intro s₁ s₂ hs
    simp [applyWord]
    exact ih (compile_step_mono types act s₁ s₂ hs)
