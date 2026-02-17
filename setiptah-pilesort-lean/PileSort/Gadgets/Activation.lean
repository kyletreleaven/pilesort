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
  let endPos := applyWord m startPos word
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
