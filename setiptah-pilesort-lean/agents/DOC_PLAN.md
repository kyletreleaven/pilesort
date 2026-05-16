# Documentation Plan

## Done (this session)

- All `/-` module headers → `/-!` across all Lean files
- `README.md` — rewrote Project Structure, removed stale Type Representations and Status
  sections, updated top-level theorem and proof stack file references
- `PLAN.md` — removed Completed section, fixed stale file name references
- `PILESHUFFLE_DESIGN.md` — deleted; key `Deck` concept migrated to doc comment
- `PROOF_STYLE.md` — moved to `agents/`
- `ClauseWord.lean` (root) — fixed `plan.md` → `PLAN.md` reference
- `Shuffle/Defs.lean` — added `Deck` doc comment (sorted-rank framing)

---

## Main result vocabulary

Goal: a newcomer reading `formulaWord_correct_multiSortable` in
`Reduction/SATToShuffle/SortableIff.lean` should understand what every term means.

| Term | File | Status |
|------|------|--------|
| `Sortable` | `Shuffle/Defs.lean` | ✓ |
| `MultiSortable` | `Shuffle/MultiRound/Defs.lean` | ✓ |
| `deckOfWord` | `ShuffleMatchingChain/ChangeProfiles.lean` | ✓ |
| `formulaWord` | `SATToMatchingChain/Defs/FormulaDefs.lean` | ✓ |
| `ALIGN` | `SATToMatchingChain/Defs/Words.lean` | ✓ |
| `HasMatchingAssignment` | `SATToShuffle/VarEncoding.lean` | ✓ |
| `satisfiesFormula` | `SAT/Defs.lean` | ✓ |
| theorem itself | `SATToShuffle/SortableIff.lean` | ✓ |

### Specific tasks

- [x] `Sortable` — add doc comment
- [x] `ALIGN` — add doc comment explaining its role in the reduction
- [x] `SortableIff.lean` — add module docstring tying the big picture together
- [x] `ChangeProfiles.lean` — fix stale comment ("will migrate here in a later step")
- [x] `SATToMatchingChain/Defs/FormulaDefs.lean` — fix `/-` header → `/-!`

---

## Broader doc comment gaps

Lower priority; address after the main result vocabulary is solid.

- [x] `Shuffle/Defs.lean` — `Deck.fromDeckSeq`, `Deck.fromCardPositions`, `shuffleRound`
- [x] `Reduction/ShuffleMultiRoundToSingle/VirtualPileTypes.lean` — `invertType`, `xorType`,
      `applyPile`, `virtualPileTypes`
- [x] `SAT/Defs.lean` — `LitPresence`
- [x] `SATToMatchingChain/VarEncoding.lean` — `litMatches`, `matchesLiteral`, `embedVars_surjective`
- [x] `MatchingChain/Defs.lean` — `Action` doc comment (ascent/descent of position, not value)

---

## Migration

- [x] Moved `VarEncoding.lean`, `VarEncodingLemmas.lean`, and `HasMatchingAssignment` to
      `SATToShuffle/`. `SATToMatchingChain` imports from there (no cycle since `VarEncoding`
      has no chain dependencies). `list_split_last` moved to `Lists.lean`.

---

## Gadget documentation

Goal: each gadget module header should explain the *role* of the gadget in the
clause-satisfaction argument, not just the automaton behavior. A reader who has
understood the top-level theorem should be able to follow the chain of gadgets
as a narrative.

- [ ] `Gadgets/Activation.lean` — explain what "activation" means: tracking whether
      the current clause has been satisfied by a literal so far
- [ ] `Gadgets/StartClause.lean` — explain what it sets up (non-activated state at
      the start of each clause test)
- [ ] `Gadgets/ForceQ.lean` — explain why it's needed (penalizes variable blocks not
      produced by Q, enforcing the variable encoding)
- [ ] `Gadgets/Alignment.lean` — explain the alignment check (the ALIGN block ensures
      the variable encoding is consistent across rounds)
- [ ] `Gadgets/Next.lean` — explain the transition role (advances from end of one
      clause gadget to the start of the next)
- [ ] `Defs/Words.lean` — expand comments on `POS`, `NEG`, `DK`, `ENDPOS`, `ENDNEG`,
      `ENDDK` to say what each tests, not just what it "administers"
