/-
  Multi-round pile shuffle.

  A `ShuffleSpec n` bundles a pile-type list with a deal assignment for one
  round.  `multiShuffleRound` applies a sequence of specs to a deck via
  `shuffleRound`, folding left.

  Note: reversing a pile index (m - 1 - x) is `Fin.rev` from core Lean.

  ## Shuffle version of formulaWord_correct

  Goal: rephrase `formulaWord_correct` in terms of `Sortable` rather than
  `accepts`, using `sortable_iff_accepts`.

  Since `sortable_iff_accepts` requires a concrete deck whose `changeProfile`
  equals the formula word, we construct one.

  ### Construction: `deckSeqNat`

  Given `word : List Action`, define `deckSeqNat : Nat → List Action → List Nat`
  by `aux start`:
    · `aux start []         = [start]`
    · `aux start (.a :: w)  = start :: aux (start+1) w`   -- start placed first
    · `aux start (.d :: w)  = aux (start+1) w ++ [start]` -- start placed last

  `deckSeqNat word = aux 0 word` is a permutation of `{0, .., word.length}`
  with the property that `indexOf k < indexOf (k+1)` iff `word[k] = .a`.

  ### Proof steps

  1. `deckSeqNat_length`   — `(aux start w).length = w.length + 1`
  2. `deckSeqNat_range`    — elements of `aux start w` are exactly `{start, .., start + w.length}`;
                             in particular all < `word.length + 1` (enabling cast to `Fin`)
  3. `deckSeqNat_nodup`    — Nodup, from the range lemma (all elements distinct)
  4. `deckOfWord`          — `Deck.fromDeckSeq` on the cast list; type `Deck (word.length + 1)`

  **Milestone**: steps 1–4 (the construction and its basic properties)

  5. `indexOf_order_iff`   — key order lemma: `indexOf k (aux start w) < indexOf (k+1) (aux start w)
                             ↔ w[k - start] = .a`; by induction using `indexOf_cons_ne` +
                             a new `indexOf_append` helper
  6. `deckOfWord_changeProfile` — `Deck.changeProfile (deckOfWord word) = word`
                             from step 5 via `changeProfile_get` + `List.ext`
  7. `formulaWord_correct_sortable` — compose `sortable_iff_accepts` +
                             `deckOfWord_changeProfile` + `formulaWord_correct`
-/
import PileSort.PileShuffle
import PileSort.VirtualPileTypes

/-- One round's worth of pile-shuffle parameters. -/
structure ShuffleSpec (n : Nat) where
  types  : List PileType
  assign : Fin n → Fin types.length

/-- Apply a sequence of shuffle rounds to a deck, left to right. -/
def multiShuffleRound {n : Nat} (d : Deck n) (rounds : List (ShuffleSpec n)) : Deck n :=
  rounds.foldl (fun acc r => shuffleRound acc r.types r.assign) d

/-! ## Two-round reduction to single round on virtual pile types -/

/-- The combined pile assignment for two rounds.
    Card c goes to virtual pile (assign2 c) * pt1.length + j, where j is:
    - assign1 c            if pt2[assign2 c] = Q  (Q preserves round-1 order)
    - Fin.rev (assign1 c)  if pt2[assign2 c] = S  (S reverses round-1 order) -/
def combinedAssign {n : Nat} (pt1 pt2 : List PileType)
    (assign1 : Fin n → Fin pt1.length)
    (assign2 : Fin n → Fin pt2.length) :
    Fin n → Fin (virtualPileTypes pt1 pt2).length :=
  fun c =>
    let j : Fin pt1.length := match pt2.get (assign2 c) with
      | .Q => assign1 c
      | .S => Fin.rev (assign1 c)
    ⟨(assign2 c).val * pt1.length + j.val,
      by rw [virtualPileTypes_length]; exact block_index_bound (assign2 c).isLt j.isLt⟩

/-- Two rounds of pile shuffle equal one round on virtual pile types with the
    combined assignment. -/
theorem shuffleRound_virtualPileTypes {n : Nat} (d : Deck n)
    (pt1 pt2 : List PileType)
    (assign1 : Fin n → Fin pt1.length)
    (assign2 : Fin n → Fin pt2.length) :
    shuffleRound (shuffleRound d pt1 assign1) pt2 assign2 =
    shuffleRound d (virtualPileTypes pt1 pt2) (combinedAssign pt1 pt2 assign1 assign2) := by
  sorry
