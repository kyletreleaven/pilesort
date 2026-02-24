
import PileSort.Mono
import PileSort.Reduction
import PileSort.Gadgets.StartClause

/-- There exists a Boolean assignment of length n whose embedding matches xs
    and that satisfies predicate P (typically satisfiesClause or satisfiesFormula). -/
def HasMatchingAssignment (n : Nat) (xs : List PileType) (P : List Bool → Prop) : Prop :=
  ∃ vars : List Bool, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q] ∧ P vars

def matchesLiteral (x: PileType) (i : Nat) (clause: Clause): Prop :=
  (.pos i ∈ clause ∧ x = .Q) ∨ (.neg i ∈ clause ∧ x = .S)

instance (x: PileType) (i : Nat) (clause: Clause) : Decidable (matchesLiteral x i clause) := by
  unfold matchesLiteral; infer_instance

/-- matchesLiteral on an embedded Bool reduces to the literal satisfaction condition. -/
theorem matchesLiteral_embedVar (b : Bool) (i : Nat) (clause : Clause) :
    matchesLiteral (embedVar b) i clause ↔
      (.pos i ∈ clause ∧ b = true) ∨ (.neg i ∈ clause ∧ b = false) := by
  cases b <;> simp [matchesLiteral, embedVar]

/-- satisfiesClause is equivalent to matchesLiteral firing at some in-range variable index. -/
theorem satisfiesClause_iff_matchesLiteral (vars : List Bool) (clause : Clause) :
    satisfiesClause vars clause ↔
      ∃ i, i < vars.length ∧ matchesLiteral (embedVar (vars.getD i false)) i clause := by
  constructor
  · rintro ⟨l, hl, hsat⟩
    cases l with
    | pos j =>
      have hsat' : vars[j]? = some true := hsat
      have hlt : j < vars.length := Decidable.byContradiction fun hc => by
        simp at hc; simp [List.getElem?_eq_none hc] at hsat'
      refine ⟨j, hlt, ?_⟩
      rw [matchesLiteral_embedVar]
      exact Or.inl ⟨hl, by simp [List.getD, hsat']⟩
    | neg j =>
      have hsat' : vars[j]? = some false := hsat
      have hlt : j < vars.length := Decidable.byContradiction fun hc => by
        simp at hc; simp [List.getElem?_eq_none hc] at hsat'
      refine ⟨j, hlt, ?_⟩
      rw [matchesLiteral_embedVar]
      exact Or.inr ⟨hl, by simp [List.getD, hsat']⟩
  · rintro ⟨i, hi, hm⟩
    rw [matchesLiteral_embedVar] at hm
    rcases hm with ⟨hmem, heq⟩ | ⟨hmem, heq⟩
    · exact ⟨.pos i, hmem, by
        show vars[i]? = some true
        simp [List.getD, List.getElem?_eq_getElem hi] at heq
        rw [List.getElem?_eq_getElem hi, heq]⟩
    · exact ⟨.neg i, hmem, by
        show vars[i]? = some false
        simp [List.getD, List.getElem?_eq_getElem hi] at heq
        rw [List.getElem?_eq_getElem hi, heq]⟩

/-- testWord consumes one block and passes control to the suffix on the tail.
    From ACTD: stays activated (ACTD on next block).
    From NACTD: activates (→ ACTD) if literal i is satisfied by x, else stays NACTD.
    From CLAUSE_DISQ: penalty propagates (≥ CLAUSE_DISQ on next block). -/
theorem testWord_consumption
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x : PileType) (rest : List PileType) (hrest : rest ≠ []) :
    let machine := compile (virtualPileTypes ALIGN (x :: rest))
    let suffixMachine := compile (virtualPileTypes ALIGN rest)
    let m := ALIGN.length
    -- from ACTD
    (applyWord (testWord i clause ++ suffix) machine ACTD =
      m + applyWord suffix suffixMachine ACTD)
    -- from CLAUSE_DISQ
    ∧ (applyWord (testWord i clause ++ suffix) machine CLAUSE_DISQ ≥
      m + applyWord suffix suffixMachine CLAUSE_DISQ)
    -- from NACTD
    ∧ (applyWord (testWord i clause ++ suffix) machine NACTD =
      m + applyWord suffix suffixMachine (if matchesLiteral x i clause then ACTD else NACTD))
    := by sorry

theorem endTestWord_consumption
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x y : PileType) (rest : List PileType)
    (hrest : rest ≠ [])
    :
    let m := ALIGN.length
    let machine := compile (virtualPileTypes ALIGN (x :: y :: rest))
    let nextGood := m + applyWord suffix (compile (virtualPileTypes ALIGN (y :: rest))) END_POS
    let nextBad := 2 * m + applyWord suffix (compile (virtualPileTypes ALIGN rest)) CHAIN_DISQ
    (applyWord (endTestWord i clause ++ suffix) machine CLAUSE_DISQ >= nextBad)
    ∧
    (if y = .Q then
      (applyWord (endTestWord i clause ++ suffix) machine ACTD = nextGood) ∧
      if matchesLiteral x i clause then
         applyWord (endTestWord i clause ++ suffix) machine NACTD = nextGood
      else
         applyWord (endTestWord i clause ++ suffix) machine NACTD >= nextBad
    else
      applyWord (endTestWord i clause ++ suffix) machine ACTD >= nextBad
      -- NACTD case is subsumed by ACTD since NACTD is closer to the end than ACTD
    )
    := by sorry

/-- clauseWord from START_POS: if a satisfying assignment matches A1, reaches END_POS;
    otherwise reaches the penalty zone. -/
theorem clauseWord_start (n : Nat) (clause : Clause)
    (A0 A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    let types := virtualPileTypes ALIGN (A0 ++ A1 ++ A2)
    let k := A0.length
    let m := ALIGN.length
    -- From START_POS with satisfying assignment: → END_POS
    (∀ vars : List Bool, vars.length = n → A1 = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars clause →
      applyWord (clauseWord n clause) (compile types) (START_POS + k * m) =
        END_POS + (k + n) * m)
    ∧
    -- From START_POS without any satisfying assignment matching A1: → penalty
    (¬ HasMatchingAssignment n A1 (satisfiesClause · clause) →
      applyWord (clauseWord n clause) (compile types) (START_POS + k * m) ≥
        CHAIN_DISQ + (k + n + 1) * m) := by
  sorry

/-- Chaining testWords from CLAUSE_DISQ: each step shifts by one block and preserves ≥ CLAUSE_DISQ.
    After k steps on range' start k, the result is ≥ k * m + (suffix result on dropped types).

    Induction on k:
    - k = 0: range' is empty, trivial.
    - k + 1: peel off testWord start via range'_succ + flatMap_cons.
      testWord_consumption (CLAUSE_DISQ case) gives ≥ m + (rest on tail).
      IH gives rest on tail ≥ k * m + (suffix on drop). Combine with omega. -/
theorem testChain_disq : ∀ (k : Nat) (start : Nat) (clause : Clause)
    (suffix : List Action) (types : List PileType), k < types.length →
    applyWord ((List.range' start k).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN types)) CLAUSE_DISQ >=
    k * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (types.drop k))) CLAUSE_DISQ
  | 0, _, _, _, _, _ => by simp
  | k + 1, start, clause, suffix, [], htypes => by simp at htypes
  | k + 1, start, clause, suffix, x :: rest, htypes => by
    simp only [List.length_cons] at htypes
    have hrest : rest ≠ [] := by intro h; subst h; simp at htypes
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have htw := (testWord_consumption start clause
      ((List.range' (start + 1) k).flatMap (fun i => testWord i clause) ++ suffix)
      x rest hrest).2.1
    have hih := testChain_disq k (start + 1) clause suffix rest (by omega)
    show _ >= (k + 1) * ALIGN.length + applyWord suffix
      (compile (virtualPileTypes ALIGN (List.drop k rest))) CLAUSE_DISQ
    rw [Nat.succ_mul]; omega

/-- testWords ++ endTestWord from CLAUSE_DISQ: chains n-1 testWords then endTestWord,
    consuming n+1 blocks total, landing at ≥ CHAIN_DISQ.

    Proof:
    1. Reassociate word as testWords ++ (endTestWord ++ suffix).
    2. testChain_disq (n-1 steps): shifts by (n-1)*m, stays ≥ CLAUSE_DISQ on drop.
    3. Decompose (A1++A2).drop(n-1) = [x,y] ++ A2 (last 2 of A1 plus A2).
    4. endTestWord_consumption CLAUSE_DISQ case: shifts by 2*m, lands ≥ CHAIN_DISQ.
    5. Arithmetic: (n-1)*m + 2*m = (n+1)*m. -/
theorem testChain_disq_end (n : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hn : n ≥ 1)
    (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    applyWord ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
              endTestWord (n - 1) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) CLAUSE_DISQ ≥
    (n + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  sorry

/-- ACTD is a trap: from ACTD, testWords stay at exactly ACTD after shifting.
    Mirrors testChain_disq but uses the ACTD equality case. -/
theorem testChain_actd : ∀ (k : Nat) (start : Nat) (clause : Clause)
    (suffix : List Action) (types : List PileType), k < types.length →
    applyWord ((List.range' start k).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN types)) ACTD =
    k * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (types.drop k))) ACTD
  | 0, _, _, _, _, _ => by simp
  | k + 1, start, clause, suffix, [], htypes => by simp at htypes
  | k + 1, start, clause, suffix, x :: rest, htypes => by
    simp only [List.length_cons] at htypes
    have hrest : rest ≠ [] := by intro h; subst h; simp at htypes
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have htw := (testWord_consumption start clause
      ((List.range' (start + 1) k).flatMap (fun i => testWord i clause) ++ suffix)
      x rest hrest).1
    have hih := testChain_actd k (start + 1) clause suffix rest (by omega)
    show _ = (k + 1) * ALIGN.length + applyWord suffix
      (compile (virtualPileTypes ALIGN (List.drop k rest))) ACTD
    rw [Nat.succ_mul, htw, hih]; omega

/-- clauseWord in consumption form from CHAIN_DISQ: consumes n+1 blocks.

    Proof: unfold clauseWord, start_clause_disq + testChain_disq_end. -/
theorem clauseWord_chain_consumption (n : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hn : n ≥ 1)
    (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    applyWord (clauseWord n clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) CHAIN_DISQ ≥
    (n + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  -- Unfold clauseWord and reassociate
  unfold clauseWord
  rw [show START_CLAUSE ++ (List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (n - 1) clause ++ suffix =
      START_CLAUSE ++ ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (n - 1) clause ++ suffix) from by simp [List.append_assoc]]
  -- A1 is nonempty
  obtain ⟨t, rest, rfl⟩ : ∃ t rest, A1 = t :: rest := by
    match A1, hA1 with | a :: as, _ => exact ⟨a, as, rfl⟩
  -- start_clause_disq: from CHAIN_DISQ, ≥ rest from CLAUSE_DISQ
  have hsc := start_clause_disq
    ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
      endTestWord (n - 1) clause ++ suffix)
    t (rest ++ A2)
  -- testChain_disq_end: from CLAUSE_DISQ, consumes n+1 blocks
  have hte := testChain_disq_end n clause suffix (t :: rest) A2 hn hA1 hA2
  exact Nat.le_trans hte (hsc)

/-- clauseWord from CHAIN_DISQ: penalty propagates unconditionally.

    English proof:
    1. Factor out A0 via applyWord_compile_append_shift:
       goal reduces to k*m + inner ≥ CHAIN_DISQ + (k+n+1)*m,
       i.e., inner ≥ CHAIN_DISQ + (n+1)*m.
    2. Apply clauseWord_chain_consumption (with empty suffix) on A1 ++ A2:
       inner ≥ (n+1)*m + applyWord [] (compile (vpt ALIGN A2)) CHAIN_DISQ
            = (n+1)*m + CHAIN_DISQ. ∎ -/
theorem clauseWord_chain (n : Nat) (clause : Clause)
    (A0 A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    let types := virtualPileTypes ALIGN (A0 ++ A1 ++ A2)
    let k := A0.length
    let m := ALIGN.length
    applyWord (clauseWord n clause) (compile types) (CHAIN_DISQ + k * m) ≥
      CHAIN_DISQ + (k + n + 1) * m := by
  simp only []
  -- 1. Factor out A0
  rw [show A0 ++ A1 ++ A2 = A0 ++ (A1 ++ A2) from List.append_assoc ..,
      virtualPileTypes_append,
      show CHAIN_DISQ + A0.length * ALIGN.length =
        (virtualPileTypes ALIGN A0).length + CHAIN_DISQ from by
        rw [virtualPileTypes_length]; omega,
      applyWord_compile_append_shift, virtualPileTypes_length]
  -- 2. Apply clauseWord_chain_consumption with empty suffix
  have hcc := clauseWord_chain_consumption n clause [] A1 A2 hn hA1 hA2
  rw [List.append_nil, show applyWord ([] : List Action)
    (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ = CHAIN_DISQ from rfl] at hcc
  -- hcc: applyWord clauseWord ... CHAIN_DISQ ≥ (n+1)*ALIGN.length + CHAIN_DISQ
  -- Goal: A0*AL + applyWord clauseWord ... CHAIN_DISQ ≥ CHAIN_DISQ + (A0+n+1)*AL
  -- 3. Arithmetic: (A0+n+1)*AL = A0*AL + (n+1)*AL, then omega combines with hcc
  rw [show A0.length + n + 1 = A0.length + (n + 1) from by omega, Nat.add_mul]
  omega

/-- Combined clauseWord correctness, assembling start and chain parts. -/
theorem clauseWord_correct (n : Nat) (clause : Clause)
    (A0 A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    let types := virtualPileTypes ALIGN (A0 ++ A1 ++ A2)
    let k := A0.length
    let m := ALIGN.length
    (∀ vars : List Bool, vars.length = n → A1 = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars clause →
      applyWord (clauseWord n clause) (compile types) (START_POS + k * m) =
        END_POS + (k + n) * m)
    ∧
    (¬ HasMatchingAssignment n A1 (satisfiesClause · clause) →
      applyWord (clauseWord n clause) (compile types) (START_POS + k * m) ≥
        CHAIN_DISQ + (k + n + 1) * m)
    ∧
    applyWord (clauseWord n clause) (compile types) (CHAIN_DISQ + k * m) ≥
      CHAIN_DISQ + (k + n + 1) * m :=
  ⟨(clauseWord_start n clause A0 A1 A2 hn hA1 hA2).1,
   (clauseWord_start n clause A0 A1 A2 hn hA1 hA2).2,
   clauseWord_chain n clause A0 A1 A2 hn hA1 hA2⟩

theorem list_split_last {α : Type} : ∀ (l : List α), l ≠ [] →
    ∃ init last, l = init ++ [last] ∧ init.length + 1 = l.length
  | [x], _ => ⟨[], x, rfl, rfl⟩
  | x :: y :: rest, _ => by
    have ⟨init, last, h, hlen⟩ := list_split_last (y :: rest) (by simp)
    exact ⟨x :: init, last, by rw [h]; simp, by simp_all [List.length_cons]⟩

/-- clauseWord from START_POS on replicated types: if a matching assignment satisfies the
    clause, reaches END_POS + n * ALIGN.length; otherwise reaches ≥ CHAIN_DISQ + block.
    Repackages clauseWord_correct parts 1 and 2 for the List.replicate m .Q form. -/
theorem clauseWord_sat (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)
    (∀ vars : List Bool, vars.length = n → xs = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars c →
      applyWord (clauseWord n c) (compile types) START_POS =
        END_POS + n * ALIGN.length)
    ∧
    (¬ HasMatchingAssignment n xs (satisfiesClause · c) →
      CHAIN_DISQ + xs.length * ALIGN.length ≤
        applyWord (clauseWord n c) (compile types) START_POS) := by
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN ([] ++ xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    have : m = (m - 1) + 1 := by omega
    rw [this, List.replicate_succ, List.flatten_cons]; simp
  rw [h_eq]
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have : m - 1 ≥ 1 := by omega
    have : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    rw [show m - 1 = (m - 2) + 1 from by omega, List.replicate_succ, List.flatten_cons]
    simp [this]
  have hcw := clauseWord_correct n c [] xs ((List.replicate (m - 1) xs).flatten) hn hxs_len hA2
  simp only [List.length_nil, Nat.zero_mul, Nat.zero_add] at hcw
  constructor
  · exact hcw.1
  · intro hno
    have := hcw.2.1 hno
    calc CHAIN_DISQ + xs.length * ALIGN.length
        = CHAIN_DISQ + (n + 1) * ALIGN.length := by rw [hxs_len]
      _ ≤ _ := this

/-- clauseWord from ≥ CHAIN_DISQ on replicated types always reaches ≥ CHAIN_DISQ + block.
    Repackages clauseWord_correct part 3 for the List.replicate m .Q form. -/
theorem clauseWord_penalty (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat) (s : Nat)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) (hs : CHAIN_DISQ ≤ s) :
    CHAIN_DISQ + xs.length * ALIGN.length ≤
      applyWord (clauseWord n c)
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q))) s := by
  -- Rewrite types to clauseWord_correct form
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN ([] ++ xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    have : m = (m - 1) + 1 := by omega
    rw [this, List.replicate_succ, List.flatten_cons]; simp
  rw [h_eq]
  -- clauseWord_correct part 3 with A0=[], A1=xs, A2=remaining
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    rw [show m - 1 = (m - 2) + 1 from by omega, List.replicate_succ, List.flatten_cons]
    simp [this]
  have hcw := (clauseWord_correct n c [] xs ((List.replicate (m - 1) xs).flatten) hn hxs_len hA2).2.2
  simp only [List.length_nil, Nat.zero_mul, Nat.zero_add] at hcw
  -- mono: result(s) ≥ result(CHAIN_DISQ) ≥ bound
  calc CHAIN_DISQ + xs.length * ALIGN.length
      = CHAIN_DISQ + (n + 1) * ALIGN.length := by rw [hxs_len]
    _ ≤ applyWord (clauseWord n c) _ CHAIN_DISQ := hcw
    _ ≤ applyWord (clauseWord n c) _ s :=
        applyWord_mono (clauseWord n c) _ hs
