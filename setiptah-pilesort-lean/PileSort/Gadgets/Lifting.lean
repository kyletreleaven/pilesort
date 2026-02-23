/-
  Lifting lemma: promotes gadget results proved by `decide` on small
  machines to corresponding results on any machine that contains the
  gadget's types as a contiguous window.
-/
import PileSort.Mono
import PileSort.VirtualPileTypes
import PileSort.Words

/-- If a word applied to a small window machine sends state s to state r
    (both strictly within the window), then on any larger machine where
    the window appears at offset A.length, the word sends
    A.length * AL + s to A.length * AL + r. -/
theorem gadget_lift_eq (word : List Action) (A window B : List PileType) (s r : Nat)
    (hs : s < (virtualPileTypes ALIGN window).length)
    (h : applyWord word (compile (virtualPileTypes ALIGN window)) s = r)
    (hr : r < (virtualPileTypes ALIGN window).length) :
    applyWord word (compile (virtualPileTypes ALIGN (A ++ window ++ B)))
      (A.length * ALIGN.length + s) = A.length * ALIGN.length + r := by
  sorry
