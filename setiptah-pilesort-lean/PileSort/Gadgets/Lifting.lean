/-
  Lifting lemmas: promote gadget results proved by `decide` on a small
  window machine to any larger machine that has the window as a prefix.

  Both lemmas take `(window B : List PileType)` — the window the gadget
  was designed for and the remainder. All known call sites use a fixed
  small window (e.g. `[st, nt]` or `[st, nt, e2]`) with `B` being the
  arbitrary tail; there is no need for a leading `A` prefix segment.
  Call sites bridge the `window ++ B` conclusion to `x :: y :: rest`
  form via `simp only [List.cons_append, List.nil_append]` or
  `simp only [List.singleton_append]`.
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
