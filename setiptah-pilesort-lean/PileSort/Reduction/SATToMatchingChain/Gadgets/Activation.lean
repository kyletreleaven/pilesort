import PileSort.MatchingChain
import PileSort.Reduction.ShuffleMultiRoundToSingle.VirtualPileTypes
import PileSort.Reduction.SATToMatchingChain.Defs.Words

/-!
  Activation gadget: tests whether the current variable's literal satisfies the
  clause, transitioning from "not yet satisfied" (NACTD) to "satisfied" (ACTD)
  if it does.  Once activated, the machine stays at ACTD regardless of subsequent
  literals.  A clause penalty state (CLAUSE_DISQ) propagates unconditionally.

  POS tests a positive literal (activates if st=Q), NEG tests a negative literal
  (activates if st=S), DK is a "don't care" (never activates).

  The end-activation variants (ENDPOS/ENDNEG/ENDDK) handle the final variable in
  a clause: if the clause is satisfied (ACTD, or matching NACTD), the machine
  reaches END_POS; otherwise it enters the chain penalty zone (≥ CHAIN_DISQ).

  Lemmas (three per gadget, one per starting state):
    - activation_correct_actd:      ACTD  → always ACTD + n
    - activation_correct_nactd:     NACTD → ACTD + n iff literal matches, else NACTD + n
    - activation_correct_disq:      CLAUSE_DISQ → ≥ CLAUSE_DISQ + n
    - end_activation_correct_actd:  ACTD  → END_POS + n if et=Q, else ≥ CHAIN_DISQ + 2n
    - end_activation_correct_nactd: NACTD → END_POS + n if et=Q and matches, else ≥ CHAIN_DISQ + 2n
    - end_activation_correct_disq:  CLAUSE_DISQ → ≥ CHAIN_DISQ + 2n

  Used by TestConsume.lean, bridged to LitPresence via testWord_mem/testWord_litMatches
  and endTestWord_mem/endTestWord_litMatches.
-/

/-- From ACTD, any word in {POS, NEG, DK} lands at ACTD + n. -/
theorem activation_correct_actd
    {w : List Action} (hw : w ∈ [POS, NEG, DK]) (st nt : PileType) :
    applyWord w (compile (virtualPileTypes ALIGN [st, nt])) ACTD = ACTD + ALIGN.length := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> decide +revert

/-- From NACTD, any word in {POS, NEG, DK} activates iff (POS∧st=Q) or (NEG∧st=S). -/
theorem activation_correct_nactd
    {w : List Action} (hw : w ∈ [POS, NEG, DK]) (st nt : PileType) :
    applyWord w (compile (virtualPileTypes ALIGN [st, nt])) NACTD =
    (if (w = POS ∧ st = .Q) ∨ (w = NEG ∧ st = .S) then ACTD else NACTD) + ALIGN.length := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> decide +revert

/-- From CLAUSE_DISQ, any word in {POS, NEG, DK} incurs a penalty: endpoint ≥ CLAUSE_DISQ + n. -/
theorem activation_correct_disq
    {w : List Action} (hw : w ∈ [POS, NEG, DK]) (st nt : PileType) :
    applyWord w (compile (virtualPileTypes ALIGN [st, nt])) CLAUSE_DISQ ≥ CLAUSE_DISQ + ALIGN.length := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> decide +revert

/-- From ACTD, any word in {ENDPOS, ENDNEG, ENDDK}: if endType=Q then exact END_POS + n,
    else ≥ CHAIN_DISQ + 2n. -/
theorem end_activation_correct_actd
    {w : List Action} (hw : w ∈ [ENDPOS, ENDNEG, ENDDK]) (st et e2 : PileType) :
    if et = PileType.Q then
      applyWord w (compile (virtualPileTypes ALIGN [st, et, e2])) ACTD = END_POS + ALIGN.length
    else
      CHAIN_DISQ + 2 * ALIGN.length ≤
        applyWord w (compile (virtualPileTypes ALIGN [st, et, e2])) ACTD := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> revert st et e2 <;> decide

/-- From NACTD, any word in {ENDPOS, ENDNEG, ENDDK}: activates (→ END_POS + n) iff endType=Q
    and (ENDPOS+Q) or (ENDNEG+S); else ≥ CHAIN_DISQ + 2n. -/
theorem end_activation_correct_nactd
    {w : List Action} (hw : w ∈ [ENDPOS, ENDNEG, ENDDK]) (st et e2 : PileType) :
    if et = PileType.Q ∧ ((w = ENDPOS ∧ st = .Q) ∨ (w = ENDNEG ∧ st = .S)) then
      applyWord w (compile (virtualPileTypes ALIGN [st, et, e2])) NACTD = END_POS + ALIGN.length
    else
      CHAIN_DISQ + 2 * ALIGN.length ≤
        applyWord w (compile (virtualPileTypes ALIGN [st, et, e2])) NACTD := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> revert st et e2 <;> decide

/-- From CLAUSE_DISQ, any word in {ENDPOS, ENDNEG, ENDDK} incurs penalty: endpoint ≥ CHAIN_DISQ + 2n. -/
theorem end_activation_correct_disq
    {w : List Action} (hw : w ∈ [ENDPOS, ENDNEG, ENDDK]) (st et e2 : PileType) :
    CHAIN_DISQ + 2 * ALIGN.length ≤
      applyWord w (compile (virtualPileTypes ALIGN [st, et, e2])) CLAUSE_DISQ := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> revert st et e2 <;> decide
