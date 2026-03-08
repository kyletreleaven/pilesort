/-
  Formula-level correctness theorems for the SAT-to-pile-sort reduction.

  Composes gadget theorems (clauseWord_correct) into the full
  formulaWord_correct: acceptance ↔ satisfying assignment.

  ## Proof strategy

  The proof is organized around `formulaState`, a tail-recursive computation
  that mirrors the clause-by-clause structure of `formulaWord`. The key
  connection is `formulaState_eq`: formulaState equals applyWord(formulaWord)
  on types with one vestigial block (clauses_.length + 2 Q-replications).

  Two lemmas about formulaState capture the full behavior:

  1. **formulaState_penalty**: If `start ≥ CHAIN_DISQ`, then formulaState
     ends at `≥ CHAIN_DISQ` (plus accumulated blocks). Each clause's
     clauseWord_correct part 3 keeps the state above CHAIN_DISQ, and
     the block accumulation adds init.length * block on top.

  2. **formulaState_sat**: If `start = START_POS`, then:
     - If all clauses in init are satisfied, the inner start stays at
       START_POS after each clause (clauseWord_correct part 1 + NEXT).
       The last clause then runs from START_POS.
     - If some clause in init is unsatisfied, clauseWord_correct part 2
       bumps the inner start to ≥ CHAIN_DISQ, and formulaState_penalty
       handles the remaining clauses.

  These give formulaWord_correct via formulaState_eq + truncation:
  - Forward: all satisfied → formulaState ends at END_POS + n*ALIGN.length
    in the last block, which is < block, so total < types.length → accepted.
  - Backward: some unsatisfied → formulaState ≥ CHAIN_DISQ + all blocks
    ≥ types.length → truncation gives sink → not accepted.
-/
import PileSort.Mono
import PileSort.Reduction
import PileSort.ClauseWord
import PileSort.ClauseWordCorrect
import PileSort.Gadgets.Next
import PileSort.FormulaWordNew

/-- Sat form: formulaWord from START_POS reaches exact position when vars satisfies the formula.
    Proved by induction on clauses_ using clauseNext_good_consumption (step) and
    clauseWord_start_consumption sat branch (base). -/
theorem formulaWord_sat_pos' (n : Nat) (clauses_ : List Clause) (last : Clause)
    (xs : List PileType) (vars : List Bool)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hvars : vars.length = n)
    (hxs : xs = embedVars vars ++ [PileType.Q])
    (hsat : satisfiesFormula vars (clauses_ ++ [last])) :
    applyWord (formulaWord n (clauses_ ++ [last]))
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
        (List.replicate (clauses_.length + 2) .Q))) START_POS =
      clauses_.length * (xs.length * ALIGN.length) + END_POS + n * ALIGN.length := by
  induction clauses_ with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_mul, Nat.zero_add]
    have hfw : formulaWord n [last] = clauseWord n last := by
      rw [show [last] = [] ++ [last] from rfl, formulaWord_split]; simp
    rw [hfw, virtualPileTypes_replicate_peel ALIGN xs 2 (by omega)]
    have hxs_ne : xs ≠ [] := by intro h; simp [h] at hxs_len
    have hA2 : (List.replicate 1 xs).flatten ≠ [] := by
      simp [List.replicate_succ, List.flatten_cons, hxs_ne]
    have hsat_last : satisfiesClause vars last := hsat last (by simp)
    have hhas : HasMatchingAssignment n xs (satisfiesClause · last) :=
      ⟨vars, hvars, hxs, hsat_last⟩
    have h := clauseWord_start_consumption n last [] xs _ hn hxs_len hA2
    rw [if_pos hhas, List.append_nil] at h
    simpa using h
  | cons c rest ih =>
    simp only [List.length_cons]
    rw [formulaWord_cons]
    have hsat_c : satisfiesClause vars c := hsat c (List.mem_cons_self c _)
    have hsat_rest : satisfiesFormula vars (rest ++ [last]) :=
      fun cl hmem => hsat cl (List.mem_cons_of_mem c hmem)
    have h_good := clauseNext_good_consumption n c xs (rest.length + 3)
      (formulaWord n (rest ++ [last])) hn hxs_len (by omega) vars hvars hxs hsat_c
    simp only [show rest.length + 3 - 1 = rest.length + 2 from by omega] at h_good
    rw [h_good, ih hsat_rest]
    have hfact : (rest.length + 1) * (xs.length * ALIGN.length) =
        xs.length * ALIGN.length + rest.length * (xs.length * ALIGN.length) := by
      rw [show rest.length + 1 = 1 + rest.length from by omega, Nat.add_mul, Nat.one_mul]
    omega

/-- ADAPTER: clauseWord_start_sat in replicated form. -/
theorem clauseWord_start_sat_rep (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1) (hm : m ≥ 2)
    (vars : List Bool) (hvars : vars.length = n)
    (hxs : xs = embedVars vars ++ [PileType.Q])
    (hsat : satisfiesClause vars c) :
    applyWord (clauseWord n c)
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)))
      START_POS = END_POS + n * ALIGN.length := by
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    match m, hm with
    | m' + 2, _ => simp [List.replicate_succ, List.flatten_cons]
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    match m, hm with
    | m' + 2, _ => simp [List.replicate_succ, List.flatten_cons, this]
  rw [h_eq]
  exact clauseWord_start_sat n c xs ((List.replicate (m - 1) xs).flatten) hn hxs_len hA2
    vars hvars hxs hsat

/-- ADAPTER: next_correct in replicated form. -/
theorem next_correct_rep (n : Nat) (xs : List PileType)
    (m : Nat)
    (hxs_len : xs.length = n + 1) (hm : m ≥ 2) :
    applyWord NEXT
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)))
      (END_POS + n * ALIGN.length) = START_POS + xs.length * ALIGN.length := by
  have h_split : (List.replicate m xs).flatten =
      xs ++ (List.replicate (m - 1) xs).flatten := by
    match m, hm with
    | m' + 2, _ => simp [List.replicate_succ, List.flatten_cons]
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp, h_split]
  rw [h_eq]
  have hk : n < (xs ++ (List.replicate (m - 1) xs).flatten).length := by simp; omega
  rw [next_correct (xs ++ (List.replicate (m - 1) xs).flatten) n hk, hxs_len]

/-- ADAPTER: clauseWord_start_nonsat in replicated form. -/
theorem clauseWord_start_nonsat_rep (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1) (hm : m ≥ 2)
    (hno : ¬ HasMatchingAssignment n xs (satisfiesClause · c)) :
    applyWord (clauseWord n c)
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)))
      START_POS ≥ CHAIN_DISQ + xs.length * ALIGN.length := by
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    match m, hm with
    | m' + 2, _ => simp [List.replicate_succ, List.flatten_cons]
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    match m, hm with
    | m' + 2, _ => simp [List.replicate_succ, List.flatten_cons, this]
  rw [h_eq]
  have h := clauseWord_start_nonsat n c xs ((List.replicate (m - 1) xs).flatten) hn hxs_len hA2 hno
  calc CHAIN_DISQ + xs.length * ALIGN.length
      = CHAIN_DISQ + (n + 1) * ALIGN.length := by rw [hxs_len]
    _ ≤ _ := h

/-- clauseWord ++ NEXT from START_POS on replicated types: if a matching assignment
    satisfies the clause, advances exactly one block; otherwise reaches ≥ CHAIN_DISQ + block.
    Derives from the consumption forms with suffix = []. -/
theorem clauseNext_sat (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)
    (∀ vars : List Bool, vars.length = n → xs = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars c →
      applyWord (clauseWord n c ++ NEXT) (compile types) START_POS =
        xs.length * ALIGN.length)
    ∧
    (¬ HasMatchingAssignment n xs (satisfiesClause · c) →
      CHAIN_DISQ + xs.length * ALIGN.length ≤
        applyWord (clauseWord n c ++ NEXT) (compile types) START_POS) := by
  simp only []
  constructor
  · intro vars hvars hxs hsat
    have h := clauseNext_good_consumption n c xs m ([] : List Action) hn hxs_len hm vars hvars hxs hsat
    simp only [] at h
    rw [List.append_nil] at h
    change _ = xs.length * ALIGN.length + START_POS at h
    unfold START_POS at h; simp at h; exact h
  · intro hno
    have h := clauseNext_bad_consumption n c xs m ([] : List Action) hn hxs_len hm hno
    simp only [] at h
    rw [List.append_nil] at h
    change _ ≥ xs.length * ALIGN.length + CHAIN_DISQ at h
    omega

/-- If all init clauses are satisfied by a matching assignment, formulaState
    accumulates blocks cleanly and the last clause runs from START_POS.

    By induction on clauses_.
    Base: trivial (0 * block + ...).
    Cons (c :: rest): satisfiesFormula gives satisfiesClause vars c and
    satisfiesFormula vars rest. clauseNext_sat part 1 gives mid = block,
    so mid - block = 0 = START_POS. IH gives the rest. -/
theorem formulaState_forward (n : Nat) (xs : List PileType)
    (clauses_ : List Clause) (last : Clause)
    (vars : List Bool)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hvars : vars.length = n)
    (hxs : xs = embedVars vars ++ [PileType.Q])
    (hsat : satisfiesFormula vars clauses_) :
    formulaState n xs clauses_ last START_POS =
      clauses_.length * (xs.length * ALIGN.length) +
      formulaState n xs [] last START_POS := by
  induction clauses_ with
  | nil => simp [formulaState]
  | cons c rest ih =>
    have hsat_c : satisfiesClause vars c := hsat c (List.mem_cons_self c rest)
    have hsat_rest : satisfiesFormula vars rest :=
      fun cl hmem => hsat cl (List.mem_cons_of_mem c hmem)
    have h_mid := (clauseNext_sat n c xs ((c :: rest).length + 2) hn hxs_len (by omega)).1
      vars hvars hxs hsat_c
    show xs.length * ALIGN.length + formulaState n xs rest last
        (applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
            (List.replicate ((c :: rest).length + 2) .Q))) START_POS
         - xs.length * ALIGN.length) =
      (c :: rest).length * (xs.length * ALIGN.length) + formulaState n xs [] last START_POS
    rw [h_mid, show xs.length * ALIGN.length - xs.length * ALIGN.length = START_POS from by
      unfold START_POS; omega]
    rw [ih hsat_rest]
    simp [List.length_cons, Nat.succ_mul]; omega

/-- If no assignment satisfies c :: rest but some assignment satisfies c,
    then no assignment satisfies rest (since xs determines vars uniquely
    via embedVars_injective). -/
theorem not_satisfiesFormula_rest (n : Nat) (xs : List PileType)
    (c : Clause) (rest : List Clause)
    (hno : ¬ HasMatchingAssignment n xs (satisfiesFormula · (c :: rest)))
    (hc : HasMatchingAssignment n xs (satisfiesClause · c)) :
    ¬ HasMatchingAssignment n xs (satisfiesFormula · rest) := by
  obtain ⟨vars₀, hvars₀, hxs₀, hsat₀⟩ := hc
  intro ⟨vars', hvars', hxs', hsat'⟩
  have heq : vars' = vars₀ := by
    have : embedVars vars' = embedVars vars₀ := by
      have := hxs₀ ▸ hxs'; simp at this; exact this.symm
    exact embedVars_injective vars' vars₀ this
  subst heq
  exact hno ⟨vars', hvars', hxs', fun cl hmem => by
    cases List.mem_cons.mp hmem with
    | inl h => exact h ▸ hsat₀
    | inr h => exact hsat' cl h⟩

/-- clauseWord ++ NEXT always advances at least one block from any starting state.
    If s = 0 = START_POS: clauseNext_sat gives ≥ block.
    If s ≥ 1 = CHAIN_DISQ: clauseWord_penalty + applyWord_ge gives ≥ CHAIN_DISQ + block > block. -/
theorem clauseNext_advance (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat) (s : Nat)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) :
    xs.length * ALIGN.length ≤
      applyWord (clauseWord n c ++ NEXT)
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q))) s := by
  by_cases hs : s = 0
  · -- s = 0 = START_POS
    subst hs
    have h := clauseNext_sat n c xs m hn hxs_len hm
    rcases Classical.em (HasMatchingAssignment n xs (satisfiesClause · c))
        with ⟨vars, hvars, hxs, hsat⟩ | hnc
    · have := h.1 vars hvars hxs hsat; unfold START_POS at this; omega
    · have := h.2 hnc; unfold START_POS at this; omega
  · -- s ≥ 1 = CHAIN_DISQ
    have : CHAIN_DISQ ≤ s := by unfold CHAIN_DISQ; omega
    have h_cw := clauseWord_penalty n c xs m s hn hxs_len hm this
    rw [applyWord_append]
    calc xs.length * ALIGN.length
        ≤ CHAIN_DISQ + xs.length * ALIGN.length := by omega
      _ ≤ applyWord (clauseWord n c) _ s := h_cw
      _ ≤ applyWord NEXT _ _ := applyWord_ge NEXT _ _

/-- If the starting state is at or above CHAIN_DISQ, then formulaState
    accumulates at least (clauses_.length + 1) full blocks plus CHAIN_DISQ. -/
theorem formulaState_penalty (n : Nat) (xs : List PileType)
    (clauses_ : List Clause) (last : Clause) (start : Nat)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hstart : CHAIN_DISQ ≤ start) :
    formulaState n xs clauses_ last start ≥
      (clauses_.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
  induction clauses_ generalizing start with
  | nil =>
    simp only [formulaState, List.length_nil, Nat.zero_add, Nat.one_mul]
    have := clauseWord_penalty n last xs 2 start hn hxs_len (by omega) hstart
    omega
  | cons c rest ih =>
    unfold formulaState; simp only []
    -- clauseWord c from start ≥ CHAIN_DISQ gives result ≥ CHAIN_DISQ + block
    have h_cw := clauseWord_penalty n c xs ((c :: rest).length + 2) start hn hxs_len (by omega) hstart
    -- NEXT doesn't decrease, so mid ≥ CHAIN_DISQ + block
    have h_mid : CHAIN_DISQ + xs.length * ALIGN.length ≤
        applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
            (List.replicate ((c :: rest).length + 2) .Q))) start := by
      rw [applyWord_append]
      exact Nat.le_trans h_cw (applyWord_ge NEXT _ _)
    -- mid - block ≥ CHAIN_DISQ
    have h_sub : CHAIN_DISQ ≤
        applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
            (List.replicate ((c :: rest).length + 2) .Q))) start
        - xs.length * ALIGN.length := by omega
    have h_ih := ih _ h_sub
    have h_arith : ((c :: rest).length + 1) * (xs.length * ALIGN.length) =
        xs.length * ALIGN.length + (rest.length + 1) * (xs.length * ALIGN.length) := by
      simp [List.length_cons, Nat.succ_mul]; omega
    rw [h_arith]
    omega

/-- If no matching assignment satisfies all init clauses, formulaState
    reaches the penalty bound.

    By induction on clauses_. Base case: clauseWord_sat part 2.
    Cons case: clauseNext_sat gives mid, then either
    formulaState_penalty (if ¬∃ satisfying c) or
    IH via not_satisfiesFormula_rest (if ∃ satisfying c). -/
theorem formulaState_penalty_start (n : Nat) (xs : List PileType)
    (clauses_ : List Clause) (last : Clause)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hno : ¬ HasMatchingAssignment n xs (satisfiesFormula · clauses_)) :
    formulaState n xs clauses_ last START_POS ≥
      (clauses_.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
  induction clauses_ with
  | nil =>
    simp only [formulaState, List.length_nil, Nat.zero_add, Nat.one_mul]
    have hno' : ¬ HasMatchingAssignment n xs (satisfiesClause · last) :=
      fun ⟨vars, hvars, hxs, _⟩ => hno ⟨vars, hvars, hxs, fun _ h => absurd h (List.not_mem_nil _)⟩
    have := (clauseWord_sat n last xs 2 hn hxs_len (by omega)).2 hno'
    omega
  | cons c rest ih =>
    let mid := applyWord (clauseWord n c ++ NEXT)
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
          (List.replicate ((c :: rest).length + 2) .Q))) START_POS
    show xs.length * ALIGN.length + formulaState n xs rest last
        (mid - xs.length * ALIGN.length) ≥ _
    have h_inner : formulaState n xs rest last (mid - xs.length * ALIGN.length) ≥
        (rest.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
      rcases Classical.em (HasMatchingAssignment n xs (satisfiesClause · c))
          with ⟨vars₀, hvars₀, hxs₀, hsat₀⟩ | hnc
      · have h_mid := (clauseNext_sat n c xs ((c :: rest).length + 2) hn hxs_len (by omega)).1
          vars₀ hvars₀ hxs₀ hsat₀
        rw [show mid = xs.length * ALIGN.length from h_mid,
            show xs.length * ALIGN.length - xs.length * ALIGN.length = START_POS from by
              unfold START_POS; omega]
        exact ih (not_satisfiesFormula_rest n xs c rest hno ⟨vars₀, hvars₀, hxs₀, hsat₀⟩)
      · have := (clauseNext_sat n c xs ((c :: rest).length + 2) hn hxs_len (by omega)).2 hnc
        exact formulaState_penalty n xs rest last _ hn hxs_len (by omega)
    have : ((c :: rest).length + 1) * (xs.length * ALIGN.length) =
        xs.length * ALIGN.length + (rest.length + 1) * (xs.length * ALIGN.length) := by
      simp [List.length_cons, Nat.succ_mul]; omega
    omega

/-- If no matching assignment satisfies all of clauses_ ++ [last], then
    formulaState reaches the penalty bound.
    Case splits on whether init (clauses_) is satisfiable:
    - No: formulaState_penalty_start.
    - Yes (some vars₀ satisfies init but not last): formulaState_forward
      gives init.length * block + formulaState([], last, START_POS),
      and clauseWord_sat part 2 bounds the last clause. -/
theorem formulaState_penalty_all (n : Nat) (xs : List PileType)
    (clauses_ : List Clause) (last : Clause)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hno : ¬ HasMatchingAssignment n xs (satisfiesFormula · (clauses_ ++ [last]))) :
    formulaState n xs clauses_ last START_POS ≥
      (clauses_.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
  rcases Classical.em (HasMatchingAssignment n xs (satisfiesFormula · clauses_))
      with ⟨vars₀, hvars₀, hxs₀, hsat₀⟩ | hno_init
  · -- vars₀ satisfies init but not last
    have hno_last : ¬ HasMatchingAssignment n xs (satisfiesClause · last) := by
      intro ⟨vars', hvars', hxs', hsat'⟩
      have : vars' = vars₀ := embedVars_injective vars' vars₀ (by
        have := hxs₀ ▸ hxs'; simp at this; exact this.symm)
      subst this
      exact hno ⟨vars', hvars', hxs', fun cl hmem => by
        rcases List.mem_append.mp hmem with h | h
        · exact hsat₀ cl h
        · exact (List.mem_singleton.mp h) ▸ hsat'⟩
    rw [formulaState_forward n xs clauses_ last vars₀ hn hxs_len hvars₀ hxs₀ hsat₀]
    simp only [formulaState, List.length_nil, Nat.zero_add]
    have := (clauseWord_sat n last xs 2 hn hxs_len (by omega)).2 hno_last
    have : clauses_.length * (xs.length * ALIGN.length) + (xs.length * ALIGN.length + CHAIN_DISQ) =
        (clauses_.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
      simp [Nat.succ_mul]; omega
    omega
  · exact formulaState_penalty_start n xs clauses_ last hn hxs_len hno_init

/-- Peeling one Q from the front of a replicated virtualPileTypes. -/
private theorem virtualPileTypes_replicate_Q_cons' (inner : List PileType) (m : Nat) :
    virtualPileTypes inner (List.replicate (m + 1) .Q) =
    inner ++ virtualPileTypes inner (List.replicate m .Q) := by
  simp [virtualPileTypes, List.replicate_succ, List.flatMap_cons, applyPile]

/-- formulaState_eq: The tail-recursive formulaState computation equals
    the direct application of formulaWord to the compiled machine. -/
theorem formulaState_eq (n : Nat) (xs : List PileType)
    (init : List Clause) (last : Clause) (start : Nat)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1) :
    formulaState n xs init last start =
      applyWord (formulaWord n (init ++ [last]))
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
          (List.replicate (init.length + 2) .Q))) start := by
  induction init generalizing start with
  | nil =>
    simp only [formulaState]
    have hfw : formulaWord n ([] ++ [last]) = clauseWord n last := by
      rw [formulaWord_split]; simp
    rw [hfw]
  | cons c rest ih =>
    unfold formulaState; simp only []
    rw [ih]
    symm
    rw [formulaWord_cons, applyWord_append]
    have h_types : virtualPileTypes (virtualPileTypes ALIGN xs)
        (List.replicate ((c :: rest).length + 2) .Q) =
      virtualPileTypes ALIGN xs ++
        virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (rest.length + 2) .Q) := by
      show virtualPileTypes _ (List.replicate (rest.length + 2 + 1) .Q) = _
      rw [virtualPileTypes_replicate_Q_cons']
    rw [h_types]
    have hmid : xs.length * ALIGN.length ≤
        applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes ALIGN xs ++
            virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (rest.length + 2) .Q)))
          start := by
      rw [← h_types]
      exact clauseNext_advance n c xs _ start hn hxs_len (by omega)
    have h_len : (virtualPileTypes ALIGN xs).length = xs.length * ALIGN.length :=
      virtualPileTypes_length ALIGN xs
    have h_shift := applyWord_compile_append_shift
        (formulaWord n (rest ++ [last]))
        (virtualPileTypes ALIGN xs)
        (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (rest.length + 2) .Q))
        (applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes ALIGN xs ++
            virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (rest.length + 2) .Q)))
          start - xs.length * ALIGN.length)
    rw [h_len] at h_shift
    rw [← h_shift]
    congr 1
    omega

/-- Satisfying case: on extended types (one vestigial block), applying formulaWord
    from START_POS lands at init.length * block + END_POS + n * ALIGN.length. -/
theorem formulaWord_sat_pos (n : Nat) (clauses : List Clause)
    (xs : List PileType) (vars : List Bool)
    (hn1 : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hn : vars.length = n)
    (hxs : xs = embedVars vars ++ [PileType.Q])
    (hsat : satisfiesFormula vars clauses)
    (hne : clauses ≠ []) :
    let types_ext := virtualPileTypes (virtualPileTypes ALIGN xs)
        (List.replicate (clauses.length + 1) .Q)
    applyWord (formulaWord n clauses) (compile types_ext) START_POS =
      (clauses.length - 1) * (xs.length * ALIGN.length) + END_POS + n * ALIGN.length := by
  intro types_ext
  -- 1. Split clauses = init ++ [last]
  obtain ⟨init, last, rfl, hlen⟩ := list_split_last clauses hne
  -- 2. formulaState_eq
  have h_eq := formulaState_eq n xs init last START_POS hn1 hxs_len
  have : init.length + 2 = (init ++ [last]).length + 1 := by omega
  rw [this] at h_eq; rw [← h_eq]
  -- 3. formulaState_forward
  have h_fwd := formulaState_forward n xs init last vars hn1 hxs_len hn hxs
    (fun cl hmem => hsat cl (List.mem_append_left _ hmem))
  rw [h_fwd]
  -- 4-5. Unfold formulaState([], last, START_POS) and apply clauseWord_sat part 1
  simp only [formulaState, List.length_nil, Nat.zero_add]
  have hsat_last : satisfiesClause vars last :=
    hsat last (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have h_cw := (clauseWord_sat n last xs 2 hn1 hxs_len (by omega)).1 vars hn hxs hsat_last
  rw [h_cw]
  -- 6. init.length = (init ++ [last]).length - 1
  have : (init ++ [last]).length - 1 = init.length := by omega
  rw [this]; omega

/-- Non-satisfying case: on extended types, applying formulaWord from START_POS
    reaches at least clauses.length * block + CHAIN_DISQ. -/
theorem formulaWord_unsat_pos (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hno : ¬ HasMatchingAssignment n xs (satisfiesFormula · clauses))
    (hne : clauses ≠ []) :
    let types_ext := virtualPileTypes (virtualPileTypes ALIGN xs)
        (List.replicate (clauses.length + 1) .Q)
    applyWord (formulaWord n clauses) (compile types_ext) START_POS ≥
      clauses.length * (xs.length * ALIGN.length) + CHAIN_DISQ := by
  intro types_ext
  -- 1. Split clauses = init ++ [last]
  obtain ⟨init, last, rfl, hlen⟩ := list_split_last clauses hne
  -- 2. formulaState_eq (types_ext has init.length + 2 Q-reps)
  have h_eq := formulaState_eq n xs init last START_POS hn hxs_len
  have : init.length + 2 = (init ++ [last]).length + 1 := by omega
  rw [this] at h_eq
  rw [← h_eq]
  -- 3. formulaState_penalty_all
  have h_pen := formulaState_penalty_all n xs init last hn hxs_len hno
  -- 4. Combine
  simp [List.length_append] at h_pen ⊢; omega


/-- Nonsat form: formulaWord from START_POS reaches the out-of-bounds zone when no assignment
    satisfies the formula. Proved by induction on clauses_ using:
    - clauseWord_start_consumption nonsat branch (base),
    - clauseNext_bad_consumption + formulaWord_chain_pos' (step, c-nonsat),
    - clauseNext_good_consumption + not_satisfiesFormula_rest + IH (step, c-sat). -/
theorem formulaWord_unsat_pos' (n : Nat) (clauses_ : List Clause) (last : Clause)
    (xs : List PileType)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hno : ¬ HasMatchingAssignment n xs (satisfiesFormula · (clauses_ ++ [last]))) :
    applyWord (formulaWord n (clauses_ ++ [last]))
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
        (List.replicate (clauses_.length + 2) .Q))) START_POS ≥
      (clauses_.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
  induction clauses_ with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_add, Nat.one_mul]
    have hfw : formulaWord n [last] = clauseWord n last := by
      rw [show [last] = [] ++ [last] from rfl, formulaWord_split]; simp
    rw [hfw, virtualPileTypes_replicate_peel ALIGN xs 2 (by omega)]
    simp only [show (2 : Nat) - 1 = 1 from rfl, List.replicate_succ, List.replicate_zero,
               List.flatten_cons, List.flatten_nil, List.append_nil]
    have hxs_ne : xs ≠ [] := by intro h; simp [h] at hxs_len
    have hno_last : ¬ HasMatchingAssignment n xs (satisfiesClause · last) := by
      intro ⟨vars, hvars, hxs', hsat'⟩
      exact hno ⟨vars, hvars, hxs', by simp [satisfiesFormula, hsat']⟩
    have h := clauseWord_start_consumption n last [] xs xs hn hxs_len hxs_ne
    rw [if_neg hno_last, List.append_nil] at h
    have hnil : applyWord ([] : List Action) (compile (virtualPileTypes ALIGN xs)) CHAIN_DISQ
        = CHAIN_DISQ := rfl
    rw [hnil, ← hxs_len] at h
    exact h
  | cons c rest ih =>
    simp only [List.length_cons, show rest.length + 1 + 2 = rest.length + 3 from by omega]
    rw [formulaWord_cons]
    have hfact : (rest.length + 1 + 1) * (xs.length * ALIGN.length) =
        xs.length * ALIGN.length + (rest.length + 1) * (xs.length * ALIGN.length) := by
      rw [show rest.length + 1 + 1 = 1 + (rest.length + 1) from by omega, Nat.add_mul, Nat.one_mul]
    rcases Classical.em (HasMatchingAssignment n xs (satisfiesClause · c)) with hc | hc
    · -- c-sat: clauseNext_good_consumption, then IH Lemma 2 for rest ++ [last]
      obtain ⟨vars', hvars', hxs', hsat_c⟩ := hc
      have h_good := clauseNext_good_consumption n c xs (rest.length + 3)
        (formulaWord n (rest ++ [last])) hn hxs_len (by omega) vars' hvars' hxs' hsat_c
      simp only [show rest.length + 3 - 1 = rest.length + 2 from by omega] at h_good
      rw [h_good]
      have hno' : ¬ HasMatchingAssignment n xs (satisfiesFormula · (rest ++ [last])) :=
        not_satisfiesFormula_rest n xs c (rest ++ [last]) hno ⟨vars', hvars', hxs', hsat_c⟩
      have h_ih := ih hno'
      omega
    · -- c-nonsat: clauseNext_bad_consumption, then formulaWord_chain_pos'
      have h_bad := clauseNext_bad_consumption n c xs (rest.length + 3)
        (formulaWord n (rest ++ [last])) hn hxs_len (by omega) hc
      simp only [show rest.length + 3 - 1 = rest.length + 2 from by omega] at h_bad
      have h_chain := formulaWord_chain_pos' n rest last xs CHAIN_DISQ hn hxs_len (by omega)
      omega

/-- accepts on types is equivalent to applyWord on extended types being < types.length. -/
theorem accepts_iff_applyWord_ext (word : List Action) (types extra : List PileType) :
    accepts types word ↔
      applyWord word (compile (types ++ extra)) 0 < types.length := by
  unfold accepts
  rw [applyWord_append_truncate word types extra 0 (Nat.zero_le _)]
  simp only [Nat.min_def]; split <;> omega

/-- Formula-level correctness (decomposed form): takes clauses as init ++ [last]. -/
theorem formulaWord_correct' (n : Nat) (clauses_ : List Clause) (last : Clause)
    (xs : List PileType)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1) :
    let types := virtualPileTypes
        (virtualPileTypes ALIGN xs)
        (List.replicate (clauses_.length + 1) PileType.Q)
    accepts types (formulaWord n (clauses_ ++ [last])) ↔
      HasMatchingAssignment n xs (satisfiesFormula · (clauses_ ++ [last])) := by
  intro types
  rw [accepts_iff_applyWord_ext _ _ (virtualPileTypes ALIGN xs),
      ← virtualPileTypes_replicate_Q_snoc,
      show clauses_.length + 1 + 1 = clauses_.length + 2 from by omega,
      show (0 : Nat) = START_POS from rfl]
  have h_len : types.length = (clauses_.length + 1) * (xs.length * ALIGN.length) := by
    rw [virtualPileTypes_replicate_Q_length, virtualPileTypes_length]
  constructor
  · -- Backward: applyWord < length → HasMatchingAssignment
    intro h
    exact Classical.byContradiction fun hno => by
      have := formulaWord_unsat_pos' n clauses_ last xs hn hxs_len hno
      rw [h_len] at h; unfold CHAIN_DISQ at this; omega
  · -- Forward: HasMatchingAssignment → applyWord < length
    intro ⟨vars, hvars, hxs, hsat⟩
    rw [formulaWord_sat_pos' n clauses_ last xs vars hn hxs_len hvars hxs hsat, h_len,
        show (clauses_.length + 1) * (xs.length * ALIGN.length) =
          clauses_.length * (xs.length * ALIGN.length) + xs.length * ALIGN.length from by
          rw [Nat.add_mul, Nat.one_mul], hxs_len]
    unfold END_POS ALIGN; simp; omega

/-- Formula-level correctness: a machine compiled from virtualPileTypes ALIGN xs,
    replicated over m clauses, accepts formulaWord n clauses iff
    xs = embedVars(vars) ++ [Q] for some assignment vars satisfying the formula. -/
theorem formulaWord_correct (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hne : clauses ≠ []) :
    accepts
      (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate clauses.length PileType.Q))
      (formulaWord n clauses)
    ↔ HasMatchingAssignment n xs (satisfiesFormula · clauses) := by
  obtain ⟨init, last, rfl, hlen⟩ := list_split_last clauses hne
  simp only [List.length_append, List.length_singleton] at *
  exact formulaWord_correct' n init last xs hn hxs_len
