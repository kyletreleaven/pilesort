import PileSort.SortableIff
import PileSort.FormulaWord
import PileSort.MultiRoundCommon

/-!
  Experimental redesign space for `PileSort.MultiRound`.

  This file is intended to host a parallel development of the multi-round
  folding/unfolding pipeline without destabilizing `PileSort/MultiRound.lean`.

  ## Motivation

  The hard local proofs in `MultiRound.lean` do not appear false; the main issue
  is that the current fold/orientation is awkward for the inverse theorems we
  want.

  The current implementation tends to treat the accumulator as "what has already
  been folded".  The alternative semantic picture under investigation here is:

  · the current round is the left/current input;
  · the accumulator represents the effect of all future rounds;
  · recursion should therefore align with `current :: future`.

  In that interpretation, the current transport/cast obligations around local
  inversion lemmas are likely symptoms of an orientation mismatch rather than of
  real mathematical difficulty.

  ## TODOs

  Current status:

  1. `foldVirtualPileTypesFuture` defined.
  2. Future-oriented `foldedSpec` defined.
  3. Future-oriented `unfoldedSpec` defined.
  4. Spec-level inverse/decomposition lemmas proved.
  5. Forward composition theorem `multiShuffleRound_eq_shuffleRound` proved.
  6. `multiSortable_iff_sortable` reproved against the spec-level design.

  Next steps in this file:

  1. Decide whether the spec-level API should become the permanent interface, or
     whether any thinner assignment-level wrappers are still worth keeping.
  2. If the spec-level design sticks, switch over at the module/import boundary.
  3. Discharge the remaining shared `sorry`s in `MultiRoundCommon.lean`
     (`combinedSpec_assoc`, `shuffleRound_virtualPileTypes`,
     `combinedSpec_splitSpec`, etc.).

  The goal is to keep names natural in this file and switch over later at the
  module/import boundary once the redesign is stable.  In particular, a major
  success criterion for this file is a clean reproving of
  `multiSortable_iff_sortable`, with the proof split as:

  · forward: composition correctness via `multiShuffleRound_eq_shuffleRound`;
  · backward: existence of an inverse decomposition via `unfoldedSpec`.

  That reproving is now complete in this sandbox file. The remaining proof work
  is in the shared binary/spec-level common layer. 
-/

/-- Fold round types in current/future orientation:
    the head of the list is the current round, and the recursive result
    represents the effect of all future rounds. -/
def foldVirtualPileTypesFuture : List (List PileType) → List PileType
  | [] => [PileType.Q]
  | current :: future => virtualPileTypes current (foldVirtualPileTypesFuture future)

/-- Fold many shuffle specs into one combined spec, in current/future
    orientation. -/
def foldedSpec {n : Nat} : List (ShuffleSpec n) → ShuffleSpec n
  | [] =>
      { types := [PileType.Q]
        assign := fun _ => ⟨0, by simp⟩ }
  | current :: future => combinedSpec current (foldedSpec future)

/-- Unfold a combined spec by splitting off the current round and recurring on
    the future suffix. -/
def unfoldedSpec {n : Nat} :
    (rounds : List (List PileType)) →
    (spec : ShuffleSpec n) →
    spec.types = foldVirtualPileTypesFuture rounds →
    List (ShuffleSpec n)
  | [], _, _ => []
  | current :: future, spec, h =>
      let split := splitSpec spec current (foldVirtualPileTypesFuture future)
        (by simpa [foldVirtualPileTypesFuture] using h)
      split.1 :: unfoldedSpec future split.2 rfl

/-- One-step equation for the future-oriented pile-type fold.
    This is just the defining equation (`rfl`), recorded only as a named rewrite
    rule in case later proofs read more clearly using it explicitly. -/
theorem foldVirtualPileTypesFuture_cons (current : List PileType)
    (future : List (List PileType)) :
    foldVirtualPileTypesFuture (current :: future) =
    virtualPileTypes current (foldVirtualPileTypesFuture future) := by
  rfl

private theorem shuffleSeq_singletonQ {n : Nat} (l : List (Fin n))
    (assign : Fin n → Fin 1) :
    shuffleSeq l [PileType.Q] assign = l := by
  have hassign : assign = fun _ => (0 : Fin 1) := by
    funext c
    exact Subsingleton.elim _ _
  cases hassign
  simp [shuffleSeq, List.finRange, collectPile, dealToPile]

private theorem deck_fromDeckSeq_toList {n : Nat} (d : Deck n) :
    Deck.fromDeckSeq d.toList d.toList_nodup d.toList_length = d := by
  apply Deck.ext
  · funext c
    apply Fin.ext
    simpa [Deck.fromDeckSeq] using Deck.toList_indexOf d c
  · funext c
    simp [Deck.fromDeckSeq, Deck.toList]

private theorem shuffleRound_singletonQ {n : Nat} (d : Deck n)
    (assign : Fin n → Fin 1) :
    shuffleRound d [PileType.Q] assign = d := by
  simpa [shuffleRound, shuffleSeq_singletonQ _ assign] using deck_fromDeckSeq_toList d

/-- Critical forward composition theorem for the future-oriented fold:
    executing many rounds left-to-right equals one round on the folded future
    spec. -/
theorem multiShuffleRound_eq_shuffleRound {n : Nat} (d : Deck n)
    (specs : List (ShuffleSpec n)) :
    let spec := foldedSpec specs
    multiShuffleRound d specs = shuffleRound d spec.types spec.assign := by
  induction specs generalizing d with
  | nil =>
      simpa [multiShuffleRound, foldedSpec] using (shuffleRound_singletonQ d (fun _ => 0)).symm
  | cons current future ih =>
      calc
        multiShuffleRound d (current :: future)
          = multiShuffleRound (shuffleRound d current.types current.assign) future := by
              rfl
        _ = shuffleRound (shuffleRound d current.types current.assign)
              (foldedSpec future).types (foldedSpec future).assign := by
              simpa using ih (shuffleRound d current.types current.assign)
        _ = shuffleRound d (combinedSpec current (foldedSpec future)).types
              (combinedSpec current (foldedSpec future)).assign := by
              simpa [combinedSpec] using
                (shuffleRound_virtualPileTypes d current.types (foldedSpec future).types
                  current.assign (foldedSpec future).assign)

/-- Empty-case left inverse: any spec over `[Q]` folds back from the empty
    unfolding, because assignments into `Fin 1` are unique. -/
theorem foldedSpec_unfoldedSpec_nil {n : Nat}
    (spec : ShuffleSpec n)
    (h : spec.types = foldVirtualPileTypesFuture []) :
    foldedSpec (unfoldedSpec [] spec h) = spec := by
  cases spec with
  | mk types assign =>
      cases h
      have hassign : assign = fun _ => (⟨0, by decide⟩ : Fin [PileType.Q].length) := by
        funext c
        apply Fin.ext
        exact by simpa using (assign c).isLt
      cases hassign
      rfl

/-- Nonempty left inverse: unfolding a combined spec against a nonempty round
    list and then folding the recovered specs gives back the original spec. -/
theorem foldedSpec_unfoldedSpec_cons {n : Nat}
    (current : List PileType)
    (future : List (List PileType))
    (spec : ShuffleSpec n)
    (h : spec.types = foldVirtualPileTypesFuture (current :: future)) :
    foldedSpec (unfoldedSpec (current :: future) spec h) = spec := by
  have hmain : ∀ (rounds : List (List PileType)) (spec : ShuffleSpec n)
      (h : spec.types = foldVirtualPileTypesFuture rounds),
      foldedSpec (unfoldedSpec rounds spec h) = spec := by
    intro rounds
    induction rounds with
    | nil =>
        intro spec h
        exact foldedSpec_unfoldedSpec_nil spec h
    | cons current future ih =>
        intro spec h
        let split := splitSpec spec current (foldVirtualPileTypesFuture future)
          (by simpa [foldVirtualPileTypesFuture] using h)
        change combinedSpec split.1 (foldedSpec (unfoldedSpec future split.2 rfl)) = spec
        rw [ih split.2 rfl]
        exact combinedSpec_splitSpec spec current (foldVirtualPileTypesFuture future)
          (by simpa [foldVirtualPileTypesFuture] using h)
  exact hmain (current :: future) spec h

/-- The types of the folded spec are exactly the future-oriented fold of the
    input round-type lists. -/
theorem foldedSpec_types {n : Nat} (specs : List (ShuffleSpec n)) :
    (foldedSpec specs).types = foldVirtualPileTypesFuture (specs.map (·.types)) := by
  induction specs with
  | nil => rfl
  | cons current future ih =>
      simpa [foldedSpec, foldVirtualPileTypesFuture, combinedSpec] using
        congrArg (virtualPileTypes current.types) ih

/-- The specs reconstructed by `unfoldedSpec` have exactly the requested round
    types. -/
theorem unfoldedSpec_types {n : Nat}
    (rounds : List (List PileType))
    (spec : ShuffleSpec n)
    (h : spec.types = foldVirtualPileTypesFuture rounds) :
    (unfoldedSpec rounds spec h).map (·.types) = rounds := by
  induction rounds generalizing spec with
  | nil =>
      rfl
  | cons current future ih =>
      let split := splitSpec spec current (foldVirtualPileTypesFuture future)
        (by simpa [foldVirtualPileTypesFuture] using h)
      simp [unfoldedSpec, splitSpec, split]
      simpa [split] using ih split.2 rfl

/-- Future-oriented equivalence between multi-round sortability and sortability
    by the folded virtual round.  Forward should use
    `multiShuffleRound_eq_shuffleRound`; backward should use `unfoldedAssign`
    together with the roundtrip lemmas above. -/
theorem multiSortable_iff_sortable {n : Nat} (d : Deck n)
    (rounds : List (List PileType)) :
    MultiSortable d rounds ↔ Sortable d (foldVirtualPileTypesFuture rounds) := by
  constructor
  · intro hmulti
    rcases hmulti with ⟨specs, htypes, hsorted⟩
    have hspecTypes :
        (foldedSpec specs).types = foldVirtualPileTypesFuture rounds := by
      calc
        (foldedSpec specs).types = foldVirtualPileTypesFuture (specs.map (·.types)) :=
          foldedSpec_types specs
        _ = foldVirtualPileTypesFuture rounds := by simpa [htypes]
    have hforward :
        multiShuffleRound d specs =
        shuffleRound d (foldedSpec specs).types (foldedSpec specs).assign := by
      simpa using multiShuffleRound_eq_shuffleRound d specs
    rw [← hspecTypes]
    refine ⟨(foldedSpec specs).assign, hforward.symm.trans hsorted⟩
  · intro hsort
    rcases hsort with ⟨assign, hsorted⟩
    let spec : ShuffleSpec n := {
      types := foldVirtualPileTypesFuture rounds
      assign := assign
    }
    have hspec : spec.types = foldVirtualPileTypesFuture rounds := rfl
    refine ⟨unfoldedSpec rounds spec hspec, unfoldedSpec_types rounds spec hspec, ?_⟩
    have hinv : foldedSpec (unfoldedSpec rounds spec hspec) = spec := by
      cases rounds with
      | nil => exact foldedSpec_unfoldedSpec_nil spec hspec
      | cons current future => exact foldedSpec_unfoldedSpec_cons current future spec hspec
    have hforward := multiShuffleRound_eq_shuffleRound d (unfoldedSpec rounds spec hspec)
    rw [hinv] at hforward
    exact hforward.trans hsorted

/-- Main reduction theorem: the deck realizing a formula word is sortable by the
    pile-sort machine iff the formula is satisfiable. -/
theorem formulaWord_correct_sortable (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hne : clauses ≠ []) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate clauses.length PileType.Q)
    Sortable (deckOfWord (formulaWord n clauses)) types ↔
      HasMatchingAssignment n xs (satisfiesFormula · clauses) := by
  intro types
  rw [sortable_iff_accepts (Nat.succ_pos _), deckOfWord_changeProfile]
  exact formulaWord_correct n clauses xs hn hxs_len hne

/-- Main reduction theorem (multi-round form): the deck realizing a formula word is
    sortable in three rounds (ALIGN, xs, replicate Q) iff the formula is satisfiable. -/
theorem formulaWord_correct_multiSortable (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hne : clauses ≠ []) :
    MultiSortable (deckOfWord (formulaWord n clauses))
      [ALIGN, xs, List.replicate clauses.length PileType.Q] ↔
      HasMatchingAssignment n xs (satisfiesFormula · clauses) := by
  rw [multiSortable_iff_sortable]
  have hbase : virtualPileTypes (List.replicate clauses.length PileType.Q) [PileType.Q] =
      List.replicate clauses.length PileType.Q := by
    simp [virtualPileTypes, applyPile]
  change Sortable (deckOfWord (formulaWord n clauses))
    (foldVirtualPileTypesFuture [ALIGN, xs, List.replicate clauses.length PileType.Q]) ↔ _
  simp [foldVirtualPileTypesFuture, hbase]
  rw [(virtualPileTypes_assoc ALIGN xs (List.replicate clauses.length PileType.Q)).symm]
  exact formulaWord_correct_sortable n clauses xs hn hxs_len hne
