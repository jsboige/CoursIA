/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway's Game of Life — Oscillators and Still Lifes

Additional still-life patterns (loaf, boat, tub, pond, ship) and
oscillators (pulsar period 3, pentadecathlon period 15) extending the
foundations module `Conway.Life`.

Still-lifes are verified via `isStillLife g = true`.
Oscillators are verified via `isOscillator g n = true`.

All coordinates are listed in sorted lexicographic order (by row, then
column) so that the `step` function returns a list in the same order
and `native_decide` can verify equality by structural comparison.

The pulsar (48 cells, period 3) and pentadecathlon (12 cells, period 15)
are **borderline** for `native_decide`: they require many step
computations on non-trivial cell lists. Their theorems are kept
commented out pending an explicit local `lake build` verification. The
definitions themselves are unconditionally exported.

This module is fully proven (no gaps in the uncommented theorems).
-/

/-
  English mirror of `Oscillators.lean` (FR canonical). Convention EPIC #4980
  (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct FR + EN sibling
  files — no inline bilingual block in a single file (Option B rejected). The module
  docstring and the public theorem docstrings below differ from the FR version; the body
  signatures, proofs and tactics remain byte-identical between the two files.
-/

import Conway.Life

namespace Conway_en
open Conway
namespace Life_en
open Life

/-! ## Still lifes

We add five classical still-lifes to complement `block` and `beehive`
from `Conway.Life`:

- **Loaf**: 7-cell pattern, one of the four most common still lifes
- **Boat**: 5-cell pattern, the smallest asymmetric still life
- **Tub**: 4-cell pattern, smallest still life with rotational symmetry
- **Pond**: 8-cell pattern, larger square-ish still life
- **Ship**: 6-cell pattern, related to the boat (rotated boat with extra cell)
-/

/-- The **Loaf**: a 7-cell still life.
    ```
    .XX.
    X..X
    .X.X
    ..X.
    ``` -/
def loaf : Grid :=
  [(0, 1), (0, 2), (1, 0), (1, 3), (2, 1), (2, 3), (3, 2)]

/-- The **Boat**: a 5-cell still life. Smallest asymmetric still life.
    ```
    XX.
    X.X
    .X.
    ``` -/
def boat : Grid :=
  [(0, 0), (0, 1), (1, 0), (1, 2), (2, 1)]

/-- The **Tub**: a 4-cell still life with full rotational symmetry.
    ```
    .X.
    X.X
    .X.
    ``` -/
def tub : Grid :=
  [(0, 1), (1, 0), (1, 2), (2, 1)]

/-- The **Pond**: an 8-cell still life.
    ```
    .XX.
    X..X
    X..X
    .XX.
    ``` -/
def pond : Grid :=
  [(0, 1), (0, 2), (1, 0), (1, 3), (2, 0), (2, 3), (3, 1), (3, 2)]

/-- The **Ship**: a 6-cell still life.
    ```
    XX.
    X.X
    .XX
    ``` -/
def ship : Grid :=
  [(0, 0), (0, 1), (1, 0), (1, 2), (2, 1), (2, 2)]

/-! ## Still-life verifications

Each predicate is reduced to a `Bool` by the kernel and decided by
`native_decide` after compilation. -/

-- Sanity-check evaluations (re-evaluated by `#eval` at elaboration time)
#eval isStillLife loaf
#eval isStillLife boat
#eval isStillLife tub
#eval isStillLife pond
#eval isStillLife ship

/-- The Loaf is a still life. -/
theorem loaf_still_life : isStillLife loaf = true := by native_decide

/-- The Boat is a still life. -/
theorem boat_still_life : isStillLife boat = true := by native_decide

/-- The Tub is a still life. -/
theorem tub_still_life : isStillLife tub = true := by native_decide

/-- The Pond is a still life. -/
theorem pond_still_life : isStillLife pond = true := by native_decide

/-- The Ship is a still life. -/
theorem ship_still_life : isStillLife ship = true := by native_decide

/-! ## Oscillators (borderline patterns)

These two patterns are the smallest "large" oscillators in classical
Conway's Life. They sit at the limit of what `native_decide` can
verify in a reasonable kernel budget; the witnesses below are kept as
definitions, and the theorems are commented out pending a local
`lake build` check on the target machine. If `lake build` succeeds
within the kernel reduction limit, the theorems may be uncommented.

The 13x13 layout for the pulsar follows the standard literature
positioning. The pentadecathlon is given in its minimal phase (12
cells, 10 rows by 5 columns); after 15 steps it returns to itself
modulo the canonical sort order.
-/

/-- The **Pulsar**: a 48-cell period-3 oscillator, discovered by Conway
    in 1970. The largest commonly-occurring oscillator in random soups.
    ```
    ..XXX...XXX..   row 0
    .............   row 1
    X....X.X....X   row 2
    X....X.X....X   row 3
    X....X.X....X   row 4
    ..XXX...XXX..   row 5
    .............   row 6
    ..XXX...XXX..   row 7
    X....X.X....X   row 8
    X....X.X....X   row 9
    X....X.X....X   row 10
    .............   row 11
    ..XXX...XXX..   row 12
    ``` -/
def pulsar : Grid :=
  [(0, 2),  (0, 3),  (0, 4),  (0, 8),  (0, 9),  (0, 10),
   (2, 0),  (2, 5),  (2, 7),  (2, 12),
   (3, 0),  (3, 5),  (3, 7),  (3, 12),
   (4, 0),  (4, 5),  (4, 7),  (4, 12),
   (5, 2),  (5, 3),  (5, 4),  (5, 8),  (5, 9),  (5, 10),
   (7, 2),  (7, 3),  (7, 4),  (7, 8),  (7, 9),  (7, 10),
   (8, 0),  (8, 5),  (8, 7),  (8, 12),
   (9, 0),  (9, 5),  (9, 7),  (9, 12),
   (10, 0), (10, 5), (10, 7), (10, 12),
   (12, 2), (12, 3), (12, 4), (12, 8), (12, 9), (12, 10)]

-- Verify pulsar: evolve 3 steps and check equality
#eval isOscillator pulsar 3
/-- The Pulsar has period 3. -/
theorem pulsar_period_three : isOscillator pulsar 3 = true := by native_decide

/-- The **Pentadecathlon**: a 12-cell period-15 oscillator, discovered
    by Conway in 1970. Resembles a stretched-out blinker that
    "breathes" for 15 generations. Minimal-phase coordinates:
    ```
    ..X..   row 0
    ..X..   row 1
    .X.X.   row 2
    ..X..   row 3
    ..X..   row 4
    ..X..   row 5
    ..X..   row 6
    .X.X.   row 7
    ..X..   row 8
    ..X..   row 9
    ``` -/
def pentadecathlon : Grid :=
  [(0, 2),
   (1, 2),
   (2, 1), (2, 3),
   (3, 2),
   (4, 2),
   (5, 2),
   (6, 2),
   (7, 1), (7, 3),
   (8, 2),
   (9, 2)]

-- Verify pentadecathlon: evolve 15 steps and check equality
#eval isOscillator pentadecathlon 15
/-- The Pentadecathlon has period 15. -/
theorem pentadecathlon_period_15 : isOscillator pentadecathlon 15 = true := by
  native_decide

end Life_en
end Conway_en
