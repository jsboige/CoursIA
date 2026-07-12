/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway's Game of Life — Spaceships

Lightweight, Middleweight, and Heavyweight Spaceships (LWSS, MWSS, HWSS).
Period-4 spaceships, each translating 2 cells horizontally per period.

These were discovered early in the history of the Game of Life (Conway,
Guy, Berlekamp; Cambridge 1970) and are among the most common
naturally-occurring spaceships. Together with the glider they form the
family of period-4 displacement-2 spaceships of the B3/S23 rule.

Coordinate convention (inherited from `Conway.Life`):
- Each cell is a pair `(row, col) : Int × Int`.
- Patterns are stored as `List (Int × Int)` in sorted lexicographic order
  (row first, then column) so that `step` produces a list in the same
  order, enabling `native_decide` to verify equality by structural
  comparison.
- A displacement `(dr, dc)` shifts every cell by `dr` rows and `dc`
  columns. The spaceships below are east-bound: `dr = 0`, `dc = 2`.

This module is fully proven (no gaps).
-/

import Conway.Life

namespace Conway
namespace Life

/-! ## Lightweight Spaceship (LWSS)

The smallest period-4 spaceship after the glider, with 9 live cells.
Phase 1 (heading east):

```
.OOOO
O...O
....O
O..O.
```

After 4 generations the pattern reappears, translated by `(0, 2)`.
-/

/-- The **LWSS** (Lightweight Spaceship), phase 1, east-bound. -/
def lwss : Grid :=
  [(0, 1), (0, 2), (0, 3), (0, 4),
   (1, 0), (1, 4),
   (2, 4),
   (3, 0), (3, 3)]

-- Sanity checks (computed by the elaborator, not part of the proof).
#eval lwss
#eval evolve 4 lwss
#eval shift (0, 2) lwss
#eval isSpaceship lwss 4 (0, 2)

/-- The LWSS is a spaceship of period 4 and displacement `(0, 2)`. -/
theorem lwss_spaceship : isSpaceship lwss 4 (0, 2) = true := by native_decide

/-! ## Middleweight Spaceship (MWSS)

A period-4 spaceship with 11 live cells: LWSS extended by one column and
crowned with a single "hat" cell. Phase 1 (heading east):

```
.OOOOO
O....O
.....O
O...O.
..O...
```

After 4 generations the pattern reappears, translated by `(0, 2)`.
-/

/-- The **MWSS** (Middleweight Spaceship), phase 1, east-bound. -/
def mwss : Grid :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
   (1, 0), (1, 5),
   (2, 5),
   (3, 0), (3, 4),
   (4, 2)]

#eval mwss
#eval evolve 4 mwss
#eval shift (0, 2) mwss
#eval isSpaceship mwss 4 (0, 2)

/-- The MWSS is a spaceship of period 4 and displacement `(0, 2)`. -/
theorem mwss_spaceship : isSpaceship mwss 4 (0, 2) = true := by native_decide

/-! ## Heavyweight Spaceship (HWSS)

A period-4 spaceship with 13 live cells: LWSS extended by two columns and
crowned with a two-cell "hat". Phase 1 (heading east):

```
.OOOOOO
O.....O
......O
O....O.
..OO...
```

After 4 generations the pattern reappears, translated by `(0, 2)`.
-/

/-- The **HWSS** (Heavyweight Spaceship), phase 1, east-bound. -/
def hwss : Grid :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
   (1, 0), (1, 6),
   (2, 6),
   (3, 0), (3, 5),
   (4, 2), (4, 3)]

#eval hwss
#eval evolve 4 hwss
#eval shift (0, 2) hwss
#eval isSpaceship hwss 4 (0, 2)

/-- The HWSS is a spaceship of period 4 and displacement `(0, 2)`. -/
theorem hwss_spaceship : isSpaceship hwss 4 (0, 2) = true := by native_decide

end Life
end Conway
