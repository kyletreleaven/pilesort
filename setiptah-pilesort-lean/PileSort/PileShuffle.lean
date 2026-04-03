/-
  Pile shuffle sort model.

  ## Structure

  The file is layered:

  1. List-level shuffle (`dealToPile`, `collectPile`, `shuffleSeq`) — the
     mechanics of pile shuffle on a plain list, with no permutation invariants
     required.  Correctness lemmas (Nodup, length, membership, disjointness)
     live here.

  2. `Deck n` — the permutation type, with constructors and standard decks.
     Cards are identified by sorted rank: card c belongs at position c.
     A Deck carries both directions of the permutation:
       · posOf  c = position of card c  (the permutation σ)
       · cardAt k = card at position k  (σ⁻¹)

  3. `shuffleRound` — lifts `shuffleSeq` to `Deck n` via `Deck.toList` and
     `Deck.fromDeckSeq`.  The proof obligations are discharged by the list-level
     lemmas (`shuffleSeq_nodup`, `shuffleSeq_length`).

  4. `Sortable`, `shuffleRound_order` — higher-level results.

  ## Proof roadmap for `shuffleRound_virtualPileTypes`

  The central target is:

      shuffleRound (shuffleRound d pt1 assign1) pt2 assign2
        = shuffleRound d (virtualPileTypes pt1 pt2) combinedAssign

  Strategy:

  1. Prove `shuffleRound_order`: the output ordering is determined by pile
     assignment and pile type (earlier pile wins; within a pile, Q preserves
     deck order and S reverses it).

  2. Define `combinedAssign`: maps each card to a block-indexed virtual pile,
       combinedAssign c = assign2(c) * pt1.length + f(assign2 c, assign1 c)
     where f adjusts the round-1 index based on whether pt2[assign2 c] is Q
     (identity) or S (reversed block).

  3. Prove `shuffleRound_virtualPileTypes` by Deck extensionality (posOf
     agreement suffices): apply `shuffleRound_order` twice on the LHS and
     once on the RHS, then use `virtualPileTypes_getElem` to match the
     virtual pile type at the combined index to the composed condition.
-/
