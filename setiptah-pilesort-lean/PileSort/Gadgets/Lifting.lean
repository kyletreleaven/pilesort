/-
  Lifting lemma: promotes gadget results proved by `decide` on small
  machines to corresponding results on any machine that contains the
  gadget's types as a contiguous window.
-/
import PileSort.Mono
import PileSort.VirtualPileTypes
import PileSort.Words

/-- If a word applied to a small window machine sends state s to state r
    (both strictly within the window), then on any larger machine with
    the window as a prefix, the word sends s to r. -/
theorem gadget_lift_eq (word : List Action) (window B : List PileType) (s r : Nat)
    (hs : s < (virtualPileTypes ALIGN window).length)
    (h : applyWord word (compile (virtualPileTypes ALIGN window)) s = r)
    (hr : r < (virtualPileTypes ALIGN window).length) :
    applyWord word (compile (virtualPileTypes ALIGN (window ++ B))) s = r := by
  rw [virtualPileTypes_append]
  have h_trunc := applyWord_append_truncate word
    (virtualPileTypes ALIGN window) (virtualPileTypes ALIGN B) s (by omega)
  rw [h] at h_trunc
  omega

/-- If a word applied to a small window machine sends state s to a state ≥ r,
    then on any larger machine with the window as a prefix, the word sends
    s to a state ≥ r. -/
theorem gadget_lift_ge (word : List Action) (window B : List PileType) (s r : Nat)
    (hs : s ≤ (virtualPileTypes ALIGN window).length)
    (h : r ≤ applyWord word (compile (virtualPileTypes ALIGN window)) s) :
    r ≤ applyWord word (compile (virtualPileTypes ALIGN (window ++ B))) s := by
  rw [virtualPileTypes_append]
  have h_trunc := applyWord_append_truncate word
    (virtualPileTypes ALIGN window) (virtualPileTypes ALIGN B) s hs
  omega
