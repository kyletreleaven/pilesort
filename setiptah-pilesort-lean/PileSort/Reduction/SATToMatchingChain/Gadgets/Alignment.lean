import PileSort.MatchingChain
import PileSort.Reduction.ShuffleMultiRoundToSingle.VirtualPileTypes
import PileSort.Reduction.SATToMatchingChain.Defs.Words

/-!
  Alignment gadget: helps eliminate first-round pile choices that cannot be resolved
  to a valid variable block — either ALIGN or its S-dual.

  In a more permissive formulation of the reduction — where the shuffler has
  freedom to choose pile types in the first round rather than being constrained
  to exactly ALIGN — a derived gadget built on this one can be prefixed to each
  clause test to penalize any first-round configuration that does not correspond
  to a valid variable encoding.
  It is proved here but not used in the current reduction, which fixes the first
  round externally as ALIGN.

  Mirrors test_align_aligned and test_align_unaligned from test_words.py.
-/

set_option maxRecDepth 4096

/-- The aligned-alignment property for a given types2 and start position. -/
def alignAlignedProp (types2 : List PileType) (startPos : Nat) : Prop :=
  let types := virtualPileTypes ALIGN types2
  let endPos := applyWord ALIGNMENT_CODE (compile types) startPos
  let n := ALIGN.length
  if startPos = START_POS ∧ types2.take 2 = [PileType.Q, PileType.S] then
    endPos = START_POS + 2 * n
  else
    endPos ≥ CHAIN_DISQ + 2 * n

instance (types2 : List PileType) (startPos : Nat) :
    Decidable (alignAlignedProp types2 startPos) := by
  unfold alignAlignedProp; exact inferInstance

theorem align_aligned_correct :
    (∀ (t1 t2 t3 : PileType), alignAlignedProp [t1, t2, t3] START_POS) ∧
    (∀ (t1 t2 t3 : PileType), alignAlignedProp [t1, t2, t3] CHAIN_DISQ)
  := by decide

-- Enumerate all PileType lists of a given length
def allPileTypeLists : Nat → List (List PileType)
  | 0 => [[]]
  | n + 1 => (allPileTypeLists n).flatMap fun l => [PileType.Q :: l, PileType.S :: l]

/-- Direct translation of test_align_unaligned from test_words.py.
    Builds a SEEN set from aligned cases, then checks all 2^9 type strings,
    skipping those already seen, verifying penalty for each start position. -/
def checkAlignUnaligned : Bool :=
  let n := ALIGN.length
  -- Build SEEN from aligned cases (virtualPileTypes ALIGN types2 for all types2)
  let seen := (allPileTypeLists 3).foldl (fun acc types2 =>
    let vpt := virtualPileTypes ALIGN types2
    if vpt ∈ acc then acc else vpt :: acc) []
  -- Check all (align, types2) combos
  (allPileTypeLists (n + 3)).all fun types =>
    let align := types.take n
    let types2 := types.drop n
    let vpt := virtualPileTypes align types2
    if vpt ∈ seen then true
    else
      (List.range n).all fun sp =>
        decide (applyWord ALIGNMENT_CODE (compile vpt) sp ≥ (sp + 1) + 2 * n)

theorem align_unaligned_correct : checkAlignUnaligned = true := by native_decide
