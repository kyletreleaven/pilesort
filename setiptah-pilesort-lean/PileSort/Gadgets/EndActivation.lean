/-
  Proof of end-activation gadget correctness.

  Mirrors test_end_activation from test_words.py:
    For each word ∈ {ENDPOS, ENDNEG, ENDDK}, start_type ∈ {Q, S},
    start_pos ∈ {NACTD, ACTD, CLAUSE_DISQ}, end_type ∈ {Q, S}, ext2 ∈ {Q, S}:

      pile_types = virtual_pile_types(ALIGN, (start_type, end_type, ext2))

      - If start_pos = CLAUSE_DISQ or end_type ≠ Q: end_pos ≥ CHAIN_DISQ + 2n
      - Else if activated (ACTD, or ENDPOS+Q, or ENDNEG+S): end_pos = END_POS + n
      - Otherwise: end_pos ≥ CHAIN_DISQ + 2n
-/
import PileSort.Automata
import PileSort.VirtualPileTypes
import PileSort.Words

def endActivationProp (word : List Action) (startType endType ext2 : PileType)
    (startPos : Nat) : Prop :=
  let m := compile (virtualPileTypes ALIGN [startType, endType, ext2])
  let endPos := applyWord word m startPos
  let n := ALIGN.length
  if startPos = CLAUSE_DISQ ∨ endType ≠ PileType.Q then
    endPos ≥ CHAIN_DISQ + 2 * n
  else if startPos = ACTD
        ∨ (word = ENDPOS ∧ startType = PileType.Q)
        ∨ (word = ENDNEG ∧ startType = PileType.S) then
    endPos = END_POS + n
  else
    endPos ≥ CHAIN_DISQ + 2 * n

instance (word : List Action) (startType endType ext2 : PileType) (startPos : Nat) :
    Decidable (endActivationProp word startType endType ext2 startPos) := by
  unfold endActivationProp; exact inferInstance

theorem end_activation_correct :
    (∀ (st et e2 : PileType) (sp : Fin 3),
      endActivationProp ENDPOS st et e2 ([NACTD, ACTD, CLAUSE_DISQ].get sp)) ∧
    (∀ (st et e2 : PileType) (sp : Fin 3),
      endActivationProp ENDNEG st et e2 ([NACTD, ACTD, CLAUSE_DISQ].get sp)) ∧
    (∀ (st et e2 : PileType) (sp : Fin 3),
      endActivationProp ENDDK st et e2 ([NACTD, ACTD, CLAUSE_DISQ].get sp))
  := by decide
