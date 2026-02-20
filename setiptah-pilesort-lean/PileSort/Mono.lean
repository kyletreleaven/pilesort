/-
  Structural properties of compile and applyWord.

  Monotonicity, sink behavior, append decomposition, and truncation.
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

/-- applyWord decomposes over word concatenation. -/
theorem applyWord_append (w₁ w₂ : List Action) (step : Action → Nat → Nat) (s : Nat) :
    applyWord (w₁ ++ w₂) step s = applyWord w₂ step (applyWord w₁ step s) := by
  simp [applyWord, List.foldl_append]

/-- compile at a position beyond the type list (sink state) is identity. -/
theorem compile_sink (types : List PileType) (act : Action) (s : Nat)
    (hs : types.length ≤ s) :
    compile types act s = s := by
  unfold compile; rw [dif_neg (by omega)]

/-- applyWord at a sink position stays at that position. -/
theorem applyWord_sink (word : List Action) (types : List PileType) (s : Nat)
    (hs : types.length ≤ s) :
    applyWord word (compile types) s = s := by
  induction word generalizing s with
  | nil => rfl
  | cons act rest ih =>
    simp [applyWord]
    rw [compile_sink types act s hs]
    exact ih s hs

/-- applyWord never decreases the state. -/
theorem applyWord_ge (word : List Action) (types : List PileType) (s : Nat) :
    s ≤ applyWord word (compile types) s := by
  induction word generalizing s with
  | nil => exact Nat.le_refl s
  | cons act rest ih =>
    simp [applyWord]
    calc s ≤ compile types act s := compile_step_ge types act s
      _ ≤ applyWord rest (compile types) (compile types act s) := ih _

/-- compile on a prefix agrees with compile on the full list at positions within the prefix. -/
theorem compile_append_left (A B : List PileType) (act : Action) (s : Nat)
    (hs : s < A.length) :
    compile (A ++ B) act s = compile A act s := by
  unfold compile
  rw [dif_pos (by simp; omega), dif_pos hs, List.getElem_append_left]

/-- compile on a concatenation at a position in the right part
    equals the left length plus compile on the right part. -/
theorem compile_append_right (A B : List PileType) (act : Action) (s : Nat) :
    compile (A ++ B) act (A.length + s) = A.length + compile B act s := by
  unfold compile
  by_cases hs : s < B.length
  · -- Both sides enter the "in bounds" branch
    have h1 : A.length + s < (A ++ B).length := by simp; omega
    rw [dif_pos h1, dif_pos hs]
    have heq : (A ++ B)[A.length + s] = B[s] := by
      rw [List.getElem_append_right (by omega : A.length ≤ A.length + s)]
      congr 1; omega
    rw [heq]
    split <;> omega
  · -- Both sides enter the "out of bounds" branch
    have h1 : ¬(A.length + s < (A ++ B).length) := by simp; omega
    rw [dif_neg h1, dif_neg hs]

/-- applyWord on a concatenation at a position in the right part
    equals the left length plus applyWord on the right part alone. -/
theorem applyWord_compile_append_shift (word : List Action) (A B : List PileType) (s : Nat) :
    applyWord word (compile (A ++ B)) (A.length + s) =
    A.length + applyWord word (compile B) s := by
  induction word generalizing s with
  | nil => simp [applyWord]
  | cons act rest ih =>
    simp [applyWord, compile_append_right]
    exact ih _

/-- Word applied to a truncated machine: result is min of full result and prefix length.
    If the word on A ++ B ends within A, the word on A alone reaches the same state.
    If the word on A ++ B crosses into B, the word on A alone reaches the sink A.length. -/
theorem applyWord_append_truncate (word : List Action) (A B : List PileType) (s : Nat)
    (hs : s ≤ A.length) :
    applyWord word (compile A) s = min (applyWord word (compile (A ++ B)) s) A.length := by
  induction word generalizing s with
  | nil => simp [applyWord, Nat.min_eq_left hs]
  | cons act rest ih =>
    change applyWord rest (compile A) (compile A act s) =
      min (applyWord rest (compile (A ++ B)) (compile (A ++ B) act s)) A.length
    by_cases hlt : s < A.length
    · -- s < A.length: both compile steps agree
      have heq : compile A act s = compile (A ++ B) act s :=
        (compile_append_left A B act s hlt).symm
      have hle : compile (A ++ B) act s ≤ A.length := by
        rw [← heq]
        calc compile A act s ≤ s + 1 := compile_step_le A act s
          _ ≤ A.length := by omega
      rw [← heq]
      exact ih (compile A act s) (heq ▸ hle)
    · -- s = A.length (sink for A)
      have hseq : s = A.length := by omega
      subst hseq
      rw [compile_sink A act A.length (Nat.le_refl _)]
      rw [applyWord_sink rest A A.length (Nat.le_refl _)]
      rw [Nat.min_comm, Nat.min_eq_left]
      calc A.length
        _ ≤ compile (A ++ B) act A.length := compile_step_ge (A ++ B) act A.length
        _ ≤ applyWord rest (compile (A ++ B)) (compile (A ++ B) act A.length) :=
            applyWord_ge rest (A ++ B) _
