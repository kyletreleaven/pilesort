/-
  Monotonicity of applyWord for compiled machines.

  Key result: if s₁ ≤ s₂ then applyWord word (compile types) s₁ ≤ applyWord word (compile types) s₂

  Proof strategy:
    1. Define Machine.Monotone (step preserves ≤)
    2. Prove applyWord_mono: monotone step ⟹ monotone applyWord (induction on word)
    3. Define stepFn: a direct functional characterization of compiled step
    4. Prove stepFn is monotone (arithmetic)
    5. Prove stepFn = compiled step (connecting list-based impl to functional spec)
    6. Derive compile_monotone
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

/-! ### Functional characterization of compiled step -/

/-- Direct functional description of what compile's step does.
    For s < n: stays (s) or advances (s+1) depending on pile type and action.
    For s ≥ n: maps to n (the sink state). -/
def stepFn (types : List PileType) (act : Action) (s : Nat) : Nat :=
  if h : s < types.length then
    match act, types[s] with
    | .a, .Q | .d, .S => s
    | .a, .S | .d, .Q => s + 1
  else types.length

theorem stepFn_ge_self (types : List PileType) (act : Action) (s : Nat)
    (hs : s < types.length) :
    s ≤ stepFn types act s := by
  simp only [stepFn, hs, dite_true]
  cases act <;> cases types[s] <;> omega

theorem stepFn_le_succ (types : List PileType) (act : Action) (s : Nat)
    (hs : s < types.length) :
    stepFn types act s ≤ s + 1 := by
  simp only [stepFn, hs, dite_true]
  cases act <;> cases types[s] <;> omega

theorem stepFn_le_length (types : List PileType) (act : Action) (s : Nat) :
    stepFn types act s ≤ types.length := by
  simp only [stepFn]
  split
  · cases act <;> cases types[s] <;> omega
  · omega

/-- stepFn is monotone. -/
theorem stepFn_mono (types : List PileType) (act : Action) {s₁ s₂ : Nat} (hs : s₁ ≤ s₂) :
    stepFn types act s₁ ≤ stepFn types act s₂ := by
  by_cases h₁ : s₁ < types.length <;> by_cases h₂ : s₂ < types.length
  · -- both in bounds
    by_cases heq : s₁ = s₂
    · subst heq; exact Nat.le_refl _
    · -- s₁ < s₂, so s₁ + 1 ≤ s₂
      have hlt : s₁ + 1 ≤ s₂ := by omega
      calc stepFn types act s₁ ≤ s₁ + 1 := stepFn_le_succ types act s₁ h₁
        _ ≤ s₂ := hlt
        _ ≤ stepFn types act s₂ := stepFn_ge_self types act s₂ h₂
  · -- s₁ in bounds, s₂ out of bounds
    calc stepFn types act s₁ ≤ types.length := stepFn_le_length types act s₁
      _ = stepFn types act s₂ := by simp [stepFn, h₂]
  · -- s₁ out of bounds, s₂ in bounds: impossible
    omega
  · -- both out of bounds
    simp [stepFn, h₁, h₂]

/-! ### Connecting stepFn to compiled step -/

/-- Length of tables produced by compileAux. -/
theorem compileAux_length (types : List PileType) (k n : Nat) :
    (compileAux types k n).1.length = types.length ∧
    (compileAux types k n).2.length = types.length := by
  induction types generalizing k with
  | nil => simp [compileAux]
  | cons t rest ih =>
    simp only [compileAux]
    obtain ⟨ih1, ih2⟩ := ih (k + 1)
    cases t <;> simp [ih1, ih2]

/-- The a-table entry at index i from compileAux, when i < types.length. -/
theorem compileAux_getElem_a (types : List PileType) (k n : Nat)
    (i : Nat) (hi : i < types.length) :
    have : i < (compileAux types k n).1.length := by rw [(compileAux_length types k n).1]; exact hi
    (compileAux types k n).1[i] =
      match types[i] with
      | .Q => k + i
      | .S => min (k + i + 1) n := by
  induction types generalizing k i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons t rest ih =>
    cases t with
    | Q =>
      cases i with
      | zero => simp [compileAux, List.getElem_cons_zero]
      | succ j =>
        have hj : j < rest.length := Nat.lt_of_succ_lt_succ hi
        simp only [compileAux]
        show (k :: (compileAux rest (k + 1) n).1)[j + 1] = _
        simp only [List.getElem_cons_succ]
        rw [ih (k + 1) j hj]
        simp only [List.getElem_cons_succ]
        omega
    | S =>
      cases i with
      | zero => simp [compileAux, List.getElem_cons_zero]
      | succ j =>
        have hj : j < rest.length := Nat.lt_of_succ_lt_succ hi
        simp only [compileAux]
        show (min (k + 1) n :: (compileAux rest (k + 1) n).1)[j + 1] = _
        simp only [List.getElem_cons_succ]
        rw [ih (k + 1) j hj]
        simp only [List.getElem_cons_succ]
        omega

/-- The d-table entry at index i from compileAux, when i < types.length. -/
theorem compileAux_getElem_d (types : List PileType) (k n : Nat)
    (i : Nat) (hi : i < types.length) :
    have : i < (compileAux types k n).2.length := by rw [(compileAux_length types k n).2]; exact hi
    (compileAux types k n).2[i] =
      match types[i] with
      | .S => k + i
      | .Q => min (k + i + 1) n := by
  induction types generalizing k i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons t rest ih =>
    cases t with
    | Q =>
      cases i with
      | zero => simp [compileAux, List.getElem_cons_zero]
      | succ j =>
        have hj : j < rest.length := Nat.lt_of_succ_lt_succ hi
        simp only [compileAux]
        show (min (k + 1) n :: (compileAux rest (k + 1) n).2)[j + 1] = _
        simp only [List.getElem_cons_succ]
        rw [ih (k + 1) j hj]
        simp only [List.getElem_cons_succ]
        omega
    | S =>
      cases i with
      | zero => simp [compileAux, List.getElem_cons_zero]
      | succ j =>
        have hj : j < rest.length := Nat.lt_of_succ_lt_succ hi
        simp only [compileAux]
        show (k :: (compileAux rest (k + 1) n).2)[j + 1] = _
        simp only [List.getElem_cons_succ]
        rw [ih (k + 1) j hj]
        simp only [List.getElem_cons_succ]
        omega

/-- Compiled step equals stepFn. -/
theorem compile_step_eq_stepFn (types : List PileType) (act : Action) (s : Nat) :
    (compile types).step act s = stepFn types act s := by
  simp only [compile, Machine.step, stepFn]
  set n := types.length
  set aux := compileAux types 0 n
  have hla : aux.1.length = n := (compileAux_length types 0 n).1
  have hld : aux.2.length = n := (compileAux_length types 0 n).2
  split
  case isTrue hs =>
    -- s < n: look up in the table
    cases act with
    | a =>
      simp only []
      have hlen : s < (aux.1 ++ [n]).length := by simp [hla]; omega
      rw [show (aux.1 ++ [n]).get? s = some (aux.1 ++ [n])[s] from List.get?_eq_getElem? .. ▸ by simp [hlen]]
      simp only [Option.getD_some]
      rw [List.getElem_append_left (by rw [hla]; exact hs)]
      rw [compileAux_getElem_a types 0 n s hs]
      cases types[s] <;> simp <;> omega
    | d =>
      simp only []
      have hlen : s < (aux.2 ++ [n]).length := by simp [hld]; omega
      rw [show (aux.2 ++ [n]).get? s = some (aux.2 ++ [n])[s] from List.get?_eq_getElem? .. ▸ by simp [hlen]]
      simp only [Option.getD_some]
      rw [List.getElem_append_left (by rw [hld]; exact hs)]
      rw [compileAux_getElem_d types 0 n s hs]
      cases types[s] <;> simp <;> omega
  case isFalse hs =>
    -- s ≥ n: out of bounds or at sink
    cases act with
    | a =>
      simp only []
      by_cases hsn : s < n + 1
      · -- s = n exactly
        have heq : s = n := by omega
        subst heq
        have hlen : n < (aux.1 ++ [n]).length := by simp [hla]
        rw [show (aux.1 ++ [n]).get? n = some (aux.1 ++ [n])[n] from List.get?_eq_getElem? .. ▸ by simp [hlen]]
        simp only [Option.getD_some]
        rw [List.getElem_append_right (by rw [hla])]
        simp [hla]
      · -- s > n: get? returns none
        have : (aux.1 ++ [n]).get? s = none := by
          simp [List.get?_eq_none, hla]; omega
        rw [this]; simp [hla]
    | d =>
      simp only []
      by_cases hsn : s < n + 1
      · have heq : s = n := by omega
        subst heq
        have hlen : n < (aux.2 ++ [n]).length := by simp [hld]
        rw [show (aux.2 ++ [n]).get? n = some (aux.2 ++ [n])[n] from List.get?_eq_getElem? .. ▸ by simp [hlen]]
        simp only [Option.getD_some]
        rw [List.getElem_append_right (by rw [hld])]
        simp [hld]
      · have : (aux.2 ++ [n]).get? s = none := by
          simp [List.get?_eq_none, hld]; omega
        rw [this]; simp [hld]

/-- compile always produces monotone machines. -/
theorem compile_monotone (types : List PileType) : (compile types).Monotone := by
  intro act s₁ s₂ hs
  rw [compile_step_eq_stepFn, compile_step_eq_stepFn]
  exact stepFn_mono types act hs
