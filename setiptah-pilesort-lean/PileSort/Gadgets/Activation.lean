/-
  Activation gadget correctness: three lemmas, one per starting position.

  For any word w ∈ {POS, NEG, DK} and pile types st, nt:
    - activation_correct_actd:  from ACTD  → always ACTD + n
    - activation_correct_nactd: from NACTD → ACTD + n iff (w=POS∧st=Q) or (w=NEG∧st=S), else NACTD + n
    - activation_correct_disq:  from CLAUSE_DISQ → ≥ CLAUSE_DISQ + n  (penalty)

  These are used by TestConsume.lean, bridged to LitPresence via testWord_mem and testWord_litMatches.
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
