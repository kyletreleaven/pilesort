/-
  Proof of FORCEQ gadget correctness.

  Mirrors test_forceq from test_words.py:
    For each start_type ∈ {Q, S}, start_pos ∈ {START_POS, CHAIN_DISQ}, next_type ∈ {Q, S}:
      - If start_pos = START_POS and start_type = Q: end_pos = START_POS + ALIGN.length
      - Otherwise: end_pos ≥ CHAIN_DISQ + ALIGN.length

  Note: The Python test has the assertion outside the next_type loop,
  so it only checks next_type = S. We prove the stronger claim for all next_types.
-/
import PileSort.Automata
import PileSort.VirtualPileTypes
import PileSort.Words

/-- The FORCEQ property: only (Q, START_POS) gives the exact target position;
    all other configurations incur a penalty. -/
def forceqProp (startType nextType : PileType) (startPos : Nat) : Prop :=
  let m := compile (virtualPileTypes ALIGN [startType, nextType])
  let endPos := applyWord m startPos FORCEQ
  if startPos = START_POS ∧ startType = PileType.Q
  then endPos = START_POS + ALIGN.length
  else endPos ≥ CHAIN_DISQ + ALIGN.length

instance (startType nextType : PileType) (startPos : Nat) :
    Decidable (forceqProp startType nextType startPos) := by
  unfold forceqProp
  exact inferInstance

theorem forceq_correct :
    ∀ (startType nextType : PileType) (sp : Fin 2),
      forceqProp startType nextType ([START_POS, CHAIN_DISQ].get sp)
  := by decide
