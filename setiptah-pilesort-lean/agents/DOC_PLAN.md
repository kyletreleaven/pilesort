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
| `Sortable` | `Shuffle/Defs.lean` | ✗ no doc comment |
| `MultiSortable` | `Shuffle/MultiRound/Defs.lean` | ✓ |
| `deckOfWord` | `ShuffleMatchingChain/ChangeProfiles.lean` | ✓ |
| `formulaWord` | `SATToMatchingChain/Defs/FormulaDefs.lean` | ✓ (terse) |
| `ALIGN` | `SATToMatchingChain/Defs/Words.lean` | ✗ no doc comment |
| `HasMatchingAssignment` | `SATToMatchingChain/ClauseWord.lean` | ✓ |
| `satisfiesFormula` | `SAT/Defs.lean` | ✓ |
| theorem itself | `SATToShuffle/SortableIff.lean` | ✗ no module docstring |

### Specific tasks

- [ ] `Sortable` — add doc comment
- [ ] `ALIGN` — add doc comment explaining its role in the reduction
- [ ] `SortableIff.lean` — add module docstring tying the big picture together
- [ ] `ChangeProfiles.lean` — fix stale comment ("will migrate here in a later step")
- [ ] `SATToMatchingChain/Defs/FormulaDefs.lean` — fix `/-` header → `/-!`

---

## Broader doc comment gaps

Lower priority; address after the main result vocabulary is solid.

- [ ] `Shuffle/Defs.lean` — `Deck.fromDeckSeq`, `Deck.fromCardPositions`, `shuffleRound`
- [ ] `Reduction/ShuffleMultiRoundToSingle/VirtualPileTypes.lean` — `invertType`, `xorType`,
      `applyPile`, `virtualPileTypes`
- [ ] `SAT/Defs.lean` — `LitPresence`
- [ ] `SATToMatchingChain/VarEncoding.lean` — `litMatches`, `matchesLiteral`
