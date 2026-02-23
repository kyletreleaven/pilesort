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
  -- 1. Split and reassociate: vpt ALIGN ((A ++ window) ++ B)
  --    = (vpt A ++ vpt window) ++ vpt B = vpt A ++ (vpt window ++ vpt B)
  rw [virtualPileTypes_append, virtualPileTypes_append, List.append_assoc]
  -- 2. Shift past vpt ALIGN A
  have h_len : (virtualPileTypes ALIGN A).length = A.length * ALIGN.length :=
    virtualPileTypes_length ALIGN A
  rw [← h_len, applyWord_compile_append_shift]
  congr 1
  -- 3. Truncate: connect small machine to (window ++ B) machine
  have h_trunc := applyWord_append_truncate word
    (virtualPileTypes ALIGN window) (virtualPileTypes ALIGN B) s (by omega)
  -- 4. h says small result = r, hr says r < window size, so min resolves
  rw [h] at h_trunc
  omega

/-- If a word applied to a small window machine sends state s to a state ≥ r,
    then on any larger machine with the window at offset A.length, the word sends
    A.length * AL + s to a state ≥ A.length * AL + r. -/
theorem gadget_lift_ge (word : List Action) (A window B : List PileType) (s r : Nat)
    (hs : s ≤ (virtualPileTypes ALIGN window).length)
    (h : r ≤ applyWord word (compile (virtualPileTypes ALIGN window)) s) :
    A.length * ALIGN.length + r ≤
      applyWord word (compile (virtualPileTypes ALIGN (A ++ window ++ B)))
        (A.length * ALIGN.length + s) := by
  -- 1. Split and reassociate
  rw [virtualPileTypes_append, virtualPileTypes_append, List.append_assoc]
  -- 2. Shift past vpt ALIGN A
  have h_len : (virtualPileTypes ALIGN A).length = A.length * ALIGN.length :=
    virtualPileTypes_length ALIGN A
  rw [← h_len, applyWord_compile_append_shift]
  -- 3. Truncate: result on (window ++ B) ≥ result on window alone
  have h_trunc := applyWord_append_truncate word
    (virtualPileTypes ALIGN window) (virtualPileTypes ALIGN B) s hs
  -- 4. Chain: result_big ≥ result_small ≥ r
  omega
