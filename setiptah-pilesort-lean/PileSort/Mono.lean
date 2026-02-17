/-
  Monotonicity of applyWord for compiled machines.

  Key result: for s₁ ≤ s₂ ≤ types.length,
    applyWord word (compile types) s₁ ≤ applyWord word (compile types) s₂

  Proof strategy:
    Two facts about compiled step (for s ≤ n):
      1. s ≤ step act s         (step never goes backward)
      2. step act s ≤ s + 1     (step advances by at most 1)
    From s₁ < s₂: step s₁ ≤ s₁ + 1 ≤ s₂ ≤ step s₂
-/
import PileSort.Automata
import PileSort.Basic

/-- For s ≤ n, compiled step never goes backward. -/
theorem compile_step_ge (types : List PileType) (act : Action) (s : Nat)
    (h : s ≤ types.length) :
    s ≤ (compile types).step act s := by
  sorry

/-- For s ≤ n, compiled step advances by at most 1. -/
theorem compile_step_le (types : List PileType) (act : Action) (s : Nat)
    (h : s ≤ types.length) :
    (compile types).step act s ≤ s + 1 := by
  sorry

/-- Compiled step preserves ≤ for states ≤ n. -/
theorem compile_step_mono (types : List PileType) (act : Action) (s₁ s₂ : Nat)
    (hs : s₁ ≤ s₂) (h₂ : s₂ ≤ types.length) :
    (compile types).step act s₁ ≤ (compile types).step act s₂ := by
  by_cases heq : s₁ = s₂
  · subst heq; exact Nat.le_refl _
  · calc (compile types).step act s₁
        _ ≤ s₁ + 1 := compile_step_le types act s₁ (by omega)
        _ ≤ s₂ := by omega
        _ ≤ (compile types).step act s₂ := compile_step_ge types act s₂ h₂

/-- Compiled step keeps states within [0, n]. -/
theorem compile_step_bounded (types : List PileType) (act : Action) (s : Nat)
    (h : s ≤ types.length) :
    (compile types).step act s ≤ types.length := by
  calc (compile types).step act s
      _ ≤ s + 1 := compile_step_le types act s h
      _ ≤ types.length + 1 := by omega
      _ = types.length + 1 := rfl
  sorry

/-- applyWord preserves ≤ and stays bounded for compiled machines. -/
theorem applyWord_mono (word : List Action) (types : List PileType)
    {s₁ s₂ : Nat} (hs : s₁ ≤ s₂) (h₂ : s₂ ≤ types.length) :
    applyWord word (compile types) s₁ ≤ applyWord word (compile types) s₂ := by

-- revert s₁ s₂ hs h₂
induction word with
| nil =>
    simp [applyWord]
    exact hs

| cons act rest ih =>
    simp [applyWord]

    have hstep :
      (compile types).step act s₁ ≤
      (compile types).step act s₂ :=
      (compile_step_mono types) act s₁ s₂ hs h₂

    have hBound :
      (compile types).step act s₂ ≤ types.length := compile_step_bounded types act s₂ h₂
      -- separate lemma about bounds

    exact ih hstep hBound
