import PileSort.MatchingChain
import PileSort.Reduction.ShuffleMultiRoundToSingle.VirtualPileTypes
import PileSort.Reduction.SATToMatchingChain.Defs.Words

/-!
  FORCEQ gadget: enforces that the current variable block was encoded as Q (true),
  penalizing any block that was not.

  In a more permissive formulation of the reduction — where the shuffler has freedom
  to choose pile types in the third round rather than being constrained to all-Q —
  FORCEQ enforces this constraint dynamically.  It is proved here but not used in
  the current reduction, which fixes the third round externally as
  `List.replicate clauses.length PileType.Q`.

  Mirrors test_forceq from test_words.py:
    - (Q, START_POS): end_pos = START_POS + ALIGN.length  (passes through)
    - otherwise: end_pos ≥ CHAIN_DISQ + ALIGN.length  (penalized)

  Note: The Python test only checks next_type = S; we prove the stronger claim
  for all next_types.
-/

/-- The FORCEQ property: only (Q, START_POS) gives the exact target position;
    all other configurations incur a penalty. -/
def forceqProp (startType nextType : PileType) (startPos : Nat) : Prop :=
  let m := compile (virtualPileTypes ALIGN [startType, nextType])
  let endPos := applyWord FORCEQ m startPos
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
