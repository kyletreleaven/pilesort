/-
  Monotonicity of applyWord for compiled machines.

  Key result: if s₁ ≤ s₂ then applyWord word (compile types) s₁ ≤ applyWord word (compile types) s₂

  Proof strategy:
    1. Define Machine.Monotone (step preserves ≤)
    2. Prove applyWord_mono: monotone step ⟹ monotone applyWord (induction on word)
    3. Prove compile_monotone: compile always produces monotone machines
       (compiled tables have entries in {s, s+1, n}, so step is monotone)
-/
import PileSort.Automata
import PileSort.Basic

/-- A machine is monotone if its step function preserves ≤. -/
def Machine.Monotone (m : Machine) : Prop :=
  ∀ (act : Action) (s₁ s₂ : Nat), s₁ ≤ s₂ → m.step act s₁ ≤ m.step act s₂

/-- foldl with a monotone function preserves ≤. -/
theorem foldl_mono {f : Nat → Action → Nat}
    (hf : ∀ act s₁ s₂, s₁ ≤ s₂ → f s₁ act ≤ f s₂ act)
    (word : List Action) {s₁ s₂ : Nat} (hs : s₁ ≤ s₂) :
    word.foldl f s₁ ≤ word.foldl f s₂ := by
  induction word generalizing s₁ s₂ with
  | nil => exact hs
  | cons act rest ih =>
    simp only [List.foldl]
    exact ih (hf act s₁ s₂ hs)

/-- applyWord preserves ≤ for monotone machines. -/
theorem applyWord_mono (word : List Action) {m : Machine} (hm : m.Monotone)
    {s₁ s₂ : Nat} (hs : s₁ ≤ s₂) :
    applyWord word m s₁ ≤ applyWord word m s₂ :=
  foldl_mono (fun act a b h => hm act a b h) word hs

/-! ### compile produces monotone machines -/

/-- Length of tables produced by compileAux. -/
theorem compileAux_length (types : List PileType) (k n : Nat) :
    (compileAux types k n).1.length = types.length ∧
    (compileAux types k n).2.length = types.length := by
  induction types generalizing k with
  | nil => simp [compileAux]
  | cons t rest ih =>
    simp only [compileAux]
    cases t <;> simp [ih (k + 1)]

/-- The a-table entry at index i from compileAux types k n, when i < types.length. -/
theorem compileAux_get_a (types : List PileType) (k n : Nat)
    (i : Nat) (hi : i < types.length) :
    (compileAux types k n).1.get ⟨i, by rw [(compileAux_length types k n).1]; exact hi⟩ =
      match types.get ⟨i, hi⟩ with
      | .Q => k + i
      | .S => min (k + i + 1) n := by
  induction types generalizing k i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons t rest ih =>
    simp only [compileAux]
    cases t with
    | Q =>
      cases i with
      | zero => simp [List.get]
      | succ j =>
        simp only [List.get]
        have hj : j < rest.length := Nat.lt_of_succ_lt_succ hi
        rw [ih rest (k + 1) n j hj]
        simp [List.get]
        omega
    | S =>
      cases i with
      | zero => simp [List.get]
      | succ j =>
        simp only [List.get]
        have hj : j < rest.length := Nat.lt_of_succ_lt_succ hi
        rw [ih rest (k + 1) n j hj]
        simp [List.get]
        omega

/-- The d-table entry at index i from compileAux types k n, when i < types.length. -/
theorem compileAux_get_d (types : List PileType) (k n : Nat)
    (i : Nat) (hi : i < types.length) :
    (compileAux types k n).2.get ⟨i, by rw [(compileAux_length types k n).2]; exact hi⟩ =
      match types.get ⟨i, hi⟩ with
      | .S => k + i
      | .Q => min (k + i + 1) n := by
  induction types generalizing k i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons t rest ih =>
    simp only [compileAux]
    cases t with
    | Q =>
      cases i with
      | zero => simp [List.get]
      | succ j =>
        simp only [List.get]
        have hj : j < rest.length := Nat.lt_of_succ_lt_succ hi
        rw [ih rest (k + 1) n j hj]
        simp [List.get]
        omega
    | S =>
      cases i with
      | zero => simp [List.get]
      | succ j =>
        simp only [List.get]
        have hj : j < rest.length := Nat.lt_of_succ_lt_succ hi
        rw [ih rest (k + 1) n j hj]
        simp [List.get]
        omega

/-- Characterize (compile types).step: for s < n, result is s or min(s+1,n);
    for s ≥ n, result is n. -/
theorem compile_step_eq (types : List PileType) (act : Action) (s : Nat) :
    (compile types).step act s =
      let n := types.length
      if h : s < n then
        match act, types.get ⟨s, h⟩ with
        | .a, .Q => s
        | .a, .S => min (s + 1) n
        | .d, .S => s
        | .d, .Q => min (s + 1) n
      else n := by
  simp only [compile, Machine.step]
  have hla := (compileAux_length types 0 types.length).1
  have hld := (compileAux_length types 0 types.length).2
  cases act with
  | a =>
    simp only []
    split
    case isTrue h =>
      have hlen : s < ((compileAux types 0 types.length).1 ++ [types.length]).length := by
        simp [hla]; omega
      rw [List.get?_eq_get hlen, Option.getD_some]
      rw [List.get_append_left (h := by rw [hla]; exact h)]
      rw [compileAux_get_a types 0 types.length s h]
      cases types.get ⟨s, h⟩ <;> simp
    case isFalse h =>
      push_neg at h
      have : s ≥ ((compileAux types 0 types.length).1 ++ [types.length]).length - 1 := by
        simp [hla]; omega
      by_cases hs : s < types.length + 1
      · have hlen : s < ((compileAux types 0 types.length).1 ++ [types.length]).length := by
          simp [hla]; omega
        rw [List.get?_eq_get hlen, Option.getD_some]
        have : s = types.length := by omega
        subst this
        rw [List.get_append_right (h := by rw [hla]; omega)]
        simp [hla]
      · push_neg at hs
        have : ((compileAux types 0 types.length).1 ++ [types.length]).get? s = none := by
          rw [List.get?_eq_none]
          simp [hla]; omega
        rw [this]
        simp [hla]
  | d =>
    simp only []
    split
    case isTrue h =>
      have hlen : s < ((compileAux types 0 types.length).2 ++ [types.length]).length := by
        simp [hld]; omega
      rw [List.get?_eq_get hlen, Option.getD_some]
      rw [List.get_append_left (h := by rw [hld]; exact h)]
      rw [compileAux_get_d types 0 types.length s h]
      cases types.get ⟨s, h⟩ <;> simp
    case isFalse h =>
      push_neg at h
      by_cases hs : s < types.length + 1
      · have hlen : s < ((compileAux types 0 types.length).2 ++ [types.length]).length := by
          simp [hld]; omega
        rw [List.get?_eq_get hlen, Option.getD_some]
        have : s = types.length := by omega
        subst this
        rw [List.get_append_right (h := by rw [hld]; omega)]
        simp [hld]
      · push_neg at hs
        have : ((compileAux types 0 types.length).2 ++ [types.length]).get? s = none := by
          rw [List.get?_eq_none]
          simp [hld]; omega
        rw [this]
        simp [hld]

/-- compile always produces monotone machines. -/
theorem compile_monotone (types : List PileType) : (compile types).Monotone := by
  intro act s₁ s₂ hs
  rw [compile_step_eq, compile_step_eq]
  set n := types.length
  split <;> split <;> rename_i h₁ h₂
  · -- s₁ < n, s₂ < n
    cases act <;> cases types.get ⟨s₁, h₁⟩ <;> cases types.get ⟨s₂, h₂⟩ <;> simp <;> omega
  · -- s₁ < n, s₂ ≥ n
    cases act <;> cases types.get ⟨s₁, h₁⟩ <;> simp <;> omega
  · -- s₁ ≥ n, s₂ < n: impossible since s₁ ≤ s₂
    omega
  · -- s₁ ≥ n, s₂ ≥ n
    omega
