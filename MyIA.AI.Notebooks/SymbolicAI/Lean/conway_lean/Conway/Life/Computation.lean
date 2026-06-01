/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway's Game of Life — Life-as-Computation

Cross-validation of the Hashlife quadtree algorithm against the reference
B3/S23 step, plus computational primitives (eaters, multi-period glider
composition). This module is part of Epic #1647 (Life-as-Computation).

Design choices:
- All predicates return `Bool` for `native_decide` compatibility.
- The `eater1` (fishhook) is the simplest signal-absorbing primitive,
  the first building block of Spartan logic gates.
- Consistency theorems `evolveHashlife n g = evolve n g` verify the
  quadtree algorithm against the list-based reference for small inputs.

This module is fully proven (no gaps).
-/

import Conway.Life
import Conway.Life.MacroCell
import Conway.Life.Hashlife

namespace Conway
namespace Life

/-! ## Section 1: Hashlife/Reference consistency

The Hashlife algorithm (`Conway.Life.Hashlife`) computes evolution via
quadtree decomposition. The reference algorithm (`step`) operates on
`List (Int × Int)` directly. The consistency theorems below verify that
both algorithms agree on canonical small patterns.

For level-2 inputs, `evolveHashlife` routes through `step4x4` (the
quadtree base case). For larger inputs, it falls back to `step`. In both
cases, the result should match `evolve n g`.
-/

/-- Hashlife and reference agree on `block` after 1 generation. -/
theorem hashlife_block_1 : evolveHashlife 1 block = evolve 1 block := by native_decide

/-- Hashlife and reference agree on `block` after 4 generations. -/
theorem hashlife_block_4 : evolveHashlife 4 block = evolve 4 block := by native_decide

/-- Hashlife and reference agree on `blinker_h` after 2 generations. -/
theorem hashlife_blinker_2 : evolveHashlife 2 blinker_h = evolve 2 blinker_h := by native_decide

/-- Hashlife and reference agree on `glider` after 4 generations. -/
theorem hashlife_glider_4 : evolveHashlife 4 glider = evolve 4 glider := by native_decide

/-- Hashlife and reference agree on `beacon` after 2 generations. -/
theorem hashlife_beacon_2 : evolveHashlife 2 beacon = evolve 2 beacon := by native_decide

/-- Hashlife and reference agree on `toad` after 2 generations. -/
theorem hashlife_toad_2 : evolveHashlife 2 toad = evolve 2 toad := by native_decide

/-! ## Section 2: Eater 1 (Fishhook) — the simplest computational sink

The **eater 1** (also called "fishhook") is a 7-cell still life discovered
by members of Conway's group at Cambridge in 1971. It is the canonical
signal-absorbing primitive in Life-as-Computation constructions: its
boundary "swallows" incoming gliders within ~4 generations, returning to
its original form.

In Spartan logic (Rendell 2000, Goucher 2014), eaters serve as:
- Signal sinks at gate outputs
- Boundary stabilisers in metapixel construction
- Absorbers at wire terminations

Coordinate layout (top-left = (0,0)):
```
XX..
X.X.
..X.
..XX
```
-/

/-- The **eater 1** (fishhook), a 7-cell still life. -/
def eater1 : Grid :=
  [(0, 0), (0, 1),
   (1, 0), (1, 2),
   (2, 2),
   (3, 2), (3, 3)]

#eval s!"Eater 1: {eater1}"
#eval s!"step(eater1) = {step eater1}"
#eval s!"isStillLife eater1 = {isStillLife eater1}"

/-- The eater 1 is a still life. -/
theorem eater1_still_life : isStillLife eater1 = true := by native_decide

/-! ## Section 3: Glider composition via multi-period evolution

The glider has period 4 and displacement `(1, -1)` per period. After
`4 * k` generations, it should equal `shift (k, -k) glider`. This
multi-period composition is the basis of signal propagation along
glider wires.

We verify for k = 1 (already in Life.lean), k = 2, and k = 3.
The k = 2 case (8 generations) also verifies via `evolveHashlife`.
-/

/-- After 8 generations (2 periods), the glider has shifted by (2, -2). -/
theorem glider_2periods : evolve 8 glider = shift (2, -2) glider := by native_decide

/-- After 12 generations (3 periods), the glider has shifted by (3, -3). -/
theorem glider_3periods : evolve 12 glider = shift (3, -3) glider := by native_decide

/-- Hashlife and reference agree on glider after 8 generations (2 periods). -/
theorem hashlife_glider_8 : evolveHashlife 8 glider = evolve 8 glider := by native_decide

/-! ## Section 4: MacroCell round-trip verification

Structural sanity check: the `Grid → MacroCell → Grid` round-trip
preserves live cells for canonical patterns. This verifies the quadtree
encoding/decoding at the MacroCell layer (independent of step/evolve).
-/

/-- Block survives the MacroCell round-trip. -/
theorem block_macrocell_roundtrip :
    (let (off, mc) := gridToMacroCellWithOffset block
     mc.toGrid off == block) = true := by native_decide

/-- Glider survives the MacroCell round-trip. -/
theorem glider_macrocell_roundtrip :
    (let (off, mc) := gridToMacroCellWithOffset glider
     mc.toGrid off == glider) = true := by native_decide

/-- Eater 1 survives the MacroCell round-trip. -/
theorem eater1_macrocell_roundtrip :
    (let (off, mc) := gridToMacroCellWithOffset eater1
     mc.toGrid off == eater1) = true := by native_decide

/-! ## Section 5: Diagnostic #eval witnesses

Larger computational witnesses verified by `#eval` (kernel evaluation)
rather than `native_decide` (kernel reduction). These demonstrate that
the Hashlife pipeline works on larger inputs and multi-step evolutions.
-/

-- Glider meets eater: after 8 steps, the combined configuration evolves
-- (no claim about exact absorption — that depends on precise geometry).
def glider_meets_eater : Grid :=
  sortDedup (glider ++ (eater1.map (fun p => (p.1, p.2 + 6))))

#eval s!"glider + eater combined: {glider_meets_eater.length} cells"
#eval s!"After 4 steps: {(evolve 4 glider_meets_eater).length} cells"
#eval s!"After 8 steps: {(evolve 8 glider_meets_eater).length} cells"

-- Cross-check: Hashlife vs reference on multi-step glider
#eval evolveHashlife 0 glider == glider
#eval evolveHashlife 1 glider == evolve 1 glider
#eval evolveHashlife 4 glider == evolve 4 glider
#eval evolveHashlife 8 glider == evolve 8 glider

-- Hashlife on the eater (still life = no change at every step)
#eval evolveHashlife 10 eater1 == eater1

/-! ## Section 6: Exponential-speedup Hashlife validation

`evolveHashlifeFast` uses the recursive Hashlife algorithm to jump
forward by `2^level` generations in a single MacroCell step. These
theorems verify correctness of the fast path against the reference
`evolve` for canonical patterns. -/

/-- `evolveHashlifeFast` agrees with reference on block after 4 gens. -/
theorem hashlife_fast_block_4 : evolveHashlifeFast 4 block = evolve 4 block := by native_decide

/-- `evolveHashlifeFast` agrees with reference on glider after 4 gens. -/
theorem hashlife_fast_glider_4 : evolveHashlifeFast 4 glider = evolve 4 glider := by native_decide

/-- `evolveHashlifeFast` agrees with reference on glider after 8 gens
    (2 full periods, displacement (2, -2)). -/
theorem hashlife_fast_glider_8 : evolveHashlifeFast 8 glider = shift (2, -2) glider := by native_decide

/-- `evolveHashlifeFast` agrees with reference on blinker after 2 gens. -/
theorem hashlife_fast_blinker_2 : evolveHashlifeFast 2 blinker_h = evolve 2 blinker_h := by native_decide

/-- `evolveHashlifeFast` agrees with reference on beacon after 2 gens. -/
theorem hashlife_fast_beacon_2 : evolveHashlifeFast 2 beacon = evolve 2 beacon := by native_decide

/-- `evolveHashlifeFast` agrees with reference on toad after 2 gens. -/
theorem hashlife_fast_toad_2 : evolveHashlifeFast 2 toad = evolve 2 toad := by native_decide

-- #eval witnesses for larger jumps (validates the recursive path)
#eval evolveHashlifeFast 16 block == evolve 16 block
#eval evolveHashlifeFast 12 glider == shift (3, -3) glider
#eval evolveHashlifeFast 4 blinker_h == blinker_h  -- period 2, 4 = 2 periods
#eval evolveHashlifeFast 10 eater1 == eater1  -- still life

end Life
end Conway
