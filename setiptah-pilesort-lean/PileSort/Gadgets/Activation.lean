/-
  Activation gadget correctness: three lemmas per gadget type, one per starting position.

  For any word w ∈ {POS, NEG, DK} and pile types st, nt:
    - activation_correct_actd:  from ACTD  → always ACTD + n
    - activation_correct_nactd: from NACTD → ACTD + n iff (w=POS∧st=Q) or (w=NEG∧st=S), else NACTD + n
    - activation_correct_disq:  from CLAUSE_DISQ → ≥ CLAUSE_DISQ + n  (penalty)

  For any word w ∈ {ENDPOS, ENDNEG, ENDDK} and pile types st, et, e2:
    - end_activation_correct_actd:  from ACTD → END_POS + n if et=Q, else ≥ CHAIN_DISQ + 2n
    - end_activation_correct_nactd: from NACTD → END_POS + n if et=Q and activation matches, else ≥ CHAIN_DISQ + 2n
    - end_activation_correct_disq:  from CLAUSE_DISQ → ≥ CHAIN_DISQ + 2n  (penalty)

  These are used by TestConsume.lean, bridged to LitPresence via testWord_mem/testWord_litMatches
  and endTestWord_mem/endTestWord_litMatches.
-/
import PileSort.Automata
import PileSort.VirtualPileTypes
import PileSort.Words

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
