/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Hashlife — the n-aware framing margin demo (P5 redesign, issue #3846)

A runnable companion to `Conway.Life.MacroCell` (`gridFrame`, `gridFrameN`)
and `Conway.Life.HashlifeCorrectness` (`box_assez_grand`, `box_assez_grandN`).
It demonstrates **concretely, at runtime**, the structural fact that motivates
the P5 redesign gate N1 (PR #5890): the fixed-2 padding of `gridFrame` caps the
light-cone margin at 2, so `box_assez_grand g n` is *unsatisfiable* for `n > 2`
on a non-empty grid, whereas the n-aware `gridFrameN n g` (padding `max 2 n`)
makes `box_assez_grandN g n` *satisfiable by construction* for every `n`.

This module is fully proven (no gaps) — every claim is discharged by
`native_decide` in `HashlifeCorrectness` (`box_assez_grandN_single_cell_3`,
`box_assez_grand_single_cell_3_false`); the `#eval` calls below only echo the
same facts at runtime for pedagogical inspection.

See Epic #3846 (Hashlife correctness, P4/P5) and the redesign verdict on that
issue for the design-gate context (N1 = framing, N2 = loop without re-framing,
N3 = P5 invariant restatement).
-/

import Conway.Life.MacroCell
import Conway.Life.HashlifeCorrectness

namespace Conway
namespace Life

/-! ## The fixed-2 cap vs the n-aware frame

`gridFrame` uses a *fixed* 2-cell padding, so the topmost live cell of any
non-empty grid sits exactly 2 cells from the MacroCell boundary. The light-cone
predicate `box_assez_grand g n` (margin `>= n` on every side) therefore holds
only for `n <= 2` and fails for any larger `n`. `gridFrameN n g` generalizes the
padding to `max 2 n`, pushing the boundary out so the margin is `>= n` by
construction. The `#eval` block below shows both frames and the resulting
predicate truth values side by side on the single-cell grid `[(0, 0)]`. -/

/-- The single-cell grid used throughout this demo. -/
def demoCell : Grid := [(0, 0)]

/- The frame chosen by the fixed-2 `gridFrame` for `demoCell`:
   top-left corner `(-2, -2)`, level `3` (side `2^3 = 8`). -/
#eval gridFrame demoCell
-- => ((-2, -2), 3)

/- The frame chosen by the n-aware `gridFrameN 3` for `demoCell`:
   padding `max 2 3 = 3`, so the corner retreats to `(-3, -3)` (still level 3). -/
#eval gridFrameN 3 demoCell
-- => ((-3, -3), 3)

/- The n-aware corner retreats further as `n` grows (padding = `max 2 n`):
   `n = 0, 2, 4` give top-left corners `(-2,-2), (-2,-2), (-4,-4)`. -/
#eval (gridFrameN 0 demoCell).1
#eval (gridFrameN 2 demoCell).1
#eval (gridFrameN 4 demoCell).1

/-! ## The margin predicate: where the two frames diverge

At `n = 2` both predicates hold (the fixed frame already offers 2 cells of
margin). At `n = 3` and beyond they split: the fixed-`gridFrame` predicate
*fails* (the `boxAssezGrand_nonempty_le_two` unsat cap), while the n-aware
`gridFrameN` predicate *holds*. This is the runtime echo of the anti-vacuity
witnesses proven in `HashlifeCorrectness`. -/

/- At `n = 2` both framings admit the margin (the fixed frame's cap is `2`). -/
#eval box_assez_grand demoCell 2   -- => true
#eval box_assez_grandN demoCell 2  -- => true

/- At `n = 3` the framings split: fixed fails (margin capped at 2), n-aware
   holds (padding `max 2 3 = 3` gives margin 3). -/
#eval box_assez_grand demoCell 3   -- => false  (the unsat cap)
#eval box_assez_grandN demoCell 3  -- => true   (gridFrameN breaks the cap)

/- The split persists at `n = 4`: fixed still fails, n-aware still holds
   (padding `max 2 4 = 4`, level grows to `4` so the domain side is `2^4`). -/
#eval box_assez_grand demoCell 4   -- => false
#eval box_assez_grandN demoCell 4  -- => true

/-! ## Why this matters for Hashlife correctness (P5)

The Game-of-Life light cone has radius `n`: over `n` generations a cell's
influence spreads by `n` in Manhattan distance. The P5 large-`n` jump theorem
needs every live cell to sit at least `n` cells from the MacroCell boundary so
nothing in its `n`-step light cone can leak out. With the fixed-2 `gridFrame`
that hypothesis is *vacuously unsatisfiable* for `n > 2`, which is the
structural obstruction to P5. `gridFrameN` makes the hypothesis carry genuine
information again — the redesign (N2 threads this frame through the jump loop
without re-framing; N3 restates the P5 invariant as "margin >= remaining n")
builds on this N1 socle. -/

end Life
end Conway
