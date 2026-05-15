# Proof Style

1. Write the simplest **natural** proof possible.
2. If a step is hard, introduce a helper as a **statement only** (sorry) — don't bend the proof to please the compiler.
3. Helpers must have **natural statements** — no implementation artifacts, no casts or reversals baked in just to make the calling proof work. The goal is *natural* proofs, not *trivial* ones.
4. Don't duplicate proof structure — **layer** instead: each lemma builds simply on what came before.
5. Don't persist with a broken approach — diagnose once, fix structurally.
6. Use **incremental sorry proofs** when stuck — sorry out each hard step, get it building green, then tackle one sorry at a time.
