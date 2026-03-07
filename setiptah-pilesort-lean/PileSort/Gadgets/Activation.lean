/-
  Proof of activation gadget correctness.

  Mirrors test_activation from test_words.py:
    For each word ∈ {POS, NEG, DK}, start_type ∈ {Q, S},
    start_pos ∈ {NACTD, ACTD, CLAUSE_DISQ}, next_type ∈ {Q, S}:

      - From CLAUSE_DISQ: end_pos ≥ CLAUSE_DISQ + n  (penalty)
      - From ACTD, or activated (POS+Q, NEG+S): end_pos = ACTD + n
      - Otherwise: end_pos = NACTD + n
-/
import PileSort.Automata
import PileSort.VirtualPileTypes
import PileSort.Words

/-- The activation property for a given word, pile types, and start position. -/
def activationProp (word : List Action) (startType nextType : PileType) (startPos : Nat) : Prop :=
  let m := compile (virtualPileTypes ALIGN [startType, nextType])
  let endPos := applyWord word m startPos
  let n := ALIGN.length
  if startPos = CLAUSE_DISQ then
    endPos ≥ CLAUSE_DISQ + n
  else if startPos = ACTD
        ∨ (word = POS ∧ startType = PileType.Q)
        ∨ (word = NEG ∧ startType = PileType.S) then
    endPos = ACTD + n
  else
    endPos = NACTD + n

instance (word : List Action) (startType nextType : PileType) (startPos : Nat) :
    Decidable (activationProp word startType nextType startPos) := by
  unfold activationProp; exact inferInstance

theorem activation_correct :
    (∀ (st nt : PileType) (sp : Fin 3),
      activationProp POS st nt ([NACTD, ACTD, CLAUSE_DISQ].get sp)) ∧
    (∀ (st nt : PileType) (sp : Fin 3),
      activationProp NEG st nt ([NACTD, ACTD, CLAUSE_DISQ].get sp)) ∧
    (∀ (st nt : PileType) (sp : Fin 3),
      activationProp DK st nt ([NACTD, ACTD, CLAUSE_DISQ].get sp))
  := by decide

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
