import PileSort.MatchingChain.Mono
import PileSort.Reduction.ShuffleMultiRoundToSingle.VirtualPileTypes
import PileSort.Reduction.SATToMatchingChain.Defs.Words

/-!
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

/-- Consumption form of gadget_lift_eq: lifts a word+suffix computation from the
    small window to the full machine, then shifts past the first block x.

    Given that `word` sends `s₀` to `s + ALIGN.length` on the window `x :: window_rest`,
    conclude that `word ++ suffix` on the full machine `x :: window_rest ++ B` gives
    `ALIGN.length + applyWord suffix (vpt (window_rest ++ B)) s`. -/
theorem gadget_lift_consumption_eq
    (word suffix : List Action) (x : PileType) (window_rest B : List PileType) (s₀ s : Nat)
    (hs₀ : s₀ < (virtualPileTypes ALIGN (x :: window_rest)).length)
    (hgadget : applyWord word (compile (virtualPileTypes ALIGN (x :: window_rest))) s₀ = s + ALIGN.length)
    (hs : s + ALIGN.length < (virtualPileTypes ALIGN (x :: window_rest)).length) :
    applyWord (word ++ suffix) (compile (virtualPileTypes ALIGN (x :: window_rest ++ B))) s₀ =
    ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN (window_rest ++ B))) s := by
  have hlift := gadget_lift_eq word (x :: window_rest) B s₀ (s + ALIGN.length) hs₀ hgadget hs
  rw [applyWord_append, hlift,
      show (x :: window_rest) ++ B = [x] ++ (window_rest ++ B) from by simp,
      virtualPileTypes_append,
      show s + ALIGN.length = (virtualPileTypes ALIGN [x]).length + s from by
        rw [virtualPileTypes_length]; simp; omega,
      applyWord_compile_append_shift, virtualPileTypes_length]
  simp

/-- Consumption form of gadget_lift_ge: lifts a word+suffix computation from the
    small window `prefix ++ [z]` to the full machine `prefix ++ z :: B`, then
    shifts past `prefix` to give a lower bound on the result.

    Given that `word` sends `s₀` to ≥ `s + |vpt prefix|` on the window `prefix ++ [z]`,
    conclude that `word ++ suffix` on the full machine `prefix ++ z :: B` gives
    ≥ `|vpt prefix| + applyWord suffix (vpt (z :: B)) s`. -/
theorem gadget_lift_consumption_ge
    (word suffix : List Action) (pfx : List PileType) (z : PileType) (B : List PileType)
    (s₀ s : Nat)
    (hs₀ : s₀ ≤ (virtualPileTypes ALIGN (pfx ++ [z])).length)
    (hgadget : s + (virtualPileTypes ALIGN pfx).length ≤
               applyWord word (compile (virtualPileTypes ALIGN (pfx ++ [z]))) s₀) :
    (virtualPileTypes ALIGN pfx).length +
        applyWord suffix (compile (virtualPileTypes ALIGN (z :: B))) s ≤
    applyWord (word ++ suffix) (compile (virtualPileTypes ALIGN (pfx ++ z :: B))) s₀ := by
  have hlift : s + (virtualPileTypes ALIGN pfx).length ≤
      applyWord word (compile (virtualPileTypes ALIGN (pfx ++ z :: B))) s₀ := by
    have h := gadget_lift_ge word (pfx ++ [z]) B s₀ (s + (virtualPileTypes ALIGN pfx).length)
      hs₀ hgadget
    simp only [List.append_assoc, List.singleton_append] at h
    exact h
  rw [applyWord_append]
  calc (virtualPileTypes ALIGN pfx).length +
          applyWord suffix (compile (virtualPileTypes ALIGN (z :: B))) s
      = applyWord suffix (compile (virtualPileTypes ALIGN (pfx ++ z :: B)))
          ((virtualPileTypes ALIGN pfx).length + s) := by
        rw [virtualPileTypes_append, ← applyWord_compile_append_shift]
    _ ≤ applyWord suffix (compile (virtualPileTypes ALIGN (pfx ++ z :: B)))
          (applyWord word (compile (virtualPileTypes ALIGN (pfx ++ z :: B))) s₀) :=
        applyWord_mono suffix _ (by omega)
