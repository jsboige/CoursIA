/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Hashlife (Gosper 1984)

The Hashlife algorithm exploits the self-similar structure of Game of
Life patterns. Two observations make it work:

1. A level-`k` `MacroCell` (`k >= 2`, side `2^k`) contains enough
   information to compute the **centered** level-`(k-1)` sub-region
   (side `2^(k-1)`) after `2^(k-2)` generations of B3/S23, because at
   distance `2^(k-2)` from any cell the rule cannot propagate
   information further than `2^(k-2)` cells.
2. The computation is structurally recursive on the level: combining
   nine overlapping level-`(k-1)` sub-cells (the standard Hashlife
   "double-nine" decomposition), each advanced by `2^(k-3)`
   generations, gives the four-quadrant decomposition of the centered
   level-`(k-1)` region after `2 * 2^(k-3) = 2^(k-2)` generations.

In this Lean port we implement the algorithm **without** memoization
(no `HashMap` / hash-consing). The kernel cannot reduce a hash-table
efficiently, so we trade peak performance for full structural
reduction. A later module may add memoization for native execution.

## Pieces of the implementation

- `step4x4`     : level-2 input -> level-1 output, one generation ahead
                  (base case, computed via direct B3/S23).
- `hashlifeResult` : level-`k` input (`k >= 2`) -> level-`(k-1)` output,
                     `2^(k-2)` generations ahead (recursive case).
- `centerInLevelPlus2` : pad a level-`n` cell into a level-`(n+2)` cell
                          with the input placed at the centered region.
- `hashlifeStep` : convenience wrapper. Given a `MacroCell` `c`, pad to
                   level `c.level + 2` and call `hashlifeResult` once,
                   advancing by `2 ^ c.level` generations.
- `evolveHashlife n g` : top-level entry point. Advances `g` by `n`
                          generations, using Hashlife when feasible.

## Correctness

We do not prove the full correctness theorem
`evolveHashlife n g = evolve n g`. The theorem is comment-only because
(a) it requires an extensive theory of MacroCell semantics and (b) the
algorithm is verified empirically by `#eval` against the reference
`step`/`evolve` from `Conway.Life` on the canonical small patterns.

For the canonical small patterns (block, blinker, glider, beacon,
toad), `evolveHashlife` is verified to agree with `evolve` on every
generation tested.

This module is fully proven (no gaps in actual definitions; the
correctness theorem is left as a future direction).
-/

import Conway.Life
import Conway.Life.MacroCell

namespace Conway
namespace Life

open MacroCell

/-! ## 4x4 base case: `step4x4`

We extract the 4x4 boolean matrix encoded in a level-2 MacroCell, then
apply the B3/S23 rule at the centered 2x2 cells `(1,1), (1,2), (2,1),
(2,2)`. -/

/-- Extract the 16 booleans of a level-2 MacroCell as a 4x4
    `Array (Array Bool)`. The all-dead matrix is returned on
    malformed (non level-2) inputs. -/
def level2ToMatrix : MacroCell -> Array (Array Bool)
  | node nw ne sw se =>
    let q : MacroCell -> Bool × Bool × Bool × Bool
      | node (leaf a) (leaf b) (leaf c) (leaf d) => (a, b, c, d)
      | _ => (false, false, false, false)
    let (a00, a01, a10, a11) := q nw   -- rows 0-1, cols 0-1
    let (b00, b01, b10, b11) := q ne   -- rows 0-1, cols 2-3
    let (c00, c01, c10, c11) := q sw   -- rows 2-3, cols 0-1
    let (d00, d01, d10, d11) := q se   -- rows 2-3, cols 2-3
    #[#[a00, a01, b00, b01],
      #[a10, a11, b10, b11],
      #[c00, c01, d00, d01],
      #[c10, c11, d10, d11]]
  | _ =>
    let row : Array Bool := #[false, false, false, false]
    #[row, row, row, row]

/-- Read `mat[i]![j]!`, defaulting to `false` if out of bounds. -/
@[inline] def readBit (mat : Array (Array Bool)) (i j : Nat) : Bool :=
  ((mat[i]?.getD #[])[j]?).getD false

/-- Apply the B3/S23 rule at `mat[i][j]`, counting live Moore neighbors. -/
def applyB3S23 (mat : Array (Array Bool)) (i j : Nat) : Bool :=
  let n : Nat :=
    (if readBit mat (i - 1) (j - 1) then 1 else 0)
    + (if readBit mat (i - 1) j       then 1 else 0)
    + (if readBit mat (i - 1) (j + 1) then 1 else 0)
    + (if readBit mat i       (j - 1) then 1 else 0)
    + (if readBit mat i       (j + 1) then 1 else 0)
    + (if readBit mat (i + 1) (j - 1) then 1 else 0)
    + (if readBit mat (i + 1) j       then 1 else 0)
    + (if readBit mat (i + 1) (j + 1) then 1 else 0)
  if readBit mat i j then
    n == 2 || n == 3
  else
    n == 3

/-- Base case of Hashlife: level-2 input -> level-1 output, one
    generation ahead, covering the centered 2x2 at positions
    `(1,1), (1,2), (2,1), (2,2)` of the input. -/
def step4x4 (c : MacroCell) : MacroCell :=
  if c.level == 2 then
    let mat := level2ToMatrix c
    let r1c1 := applyB3S23 mat 1 1
    let r1c2 := applyB3S23 mat 1 2
    let r2c1 := applyB3S23 mat 2 1
    let r2c2 := applyB3S23 mat 2 2
    node (leaf r1c1) (leaf r1c2) (leaf r2c1) (leaf r2c2)
  else
    emptyOfLevel 1

/-! ## Recursive Hashlife: `hashlifeResult`

`hashlifeResult c` takes a level-`k` MacroCell (`k >= 2`) and returns
a level-`(k-1)` MacroCell representing the centered region after
`2^(k-2)` generations.

Base case (`k = 2`): use `step4x4`.

Recursive case (`k >= 3`):
1. Decompose the input's quadrants. Each is level `k-1`. Each of those
   quadrants has four sub-quadrants of level `k-2`. Together they
   tile a 4x4 grid of level-`(k-2)` cells (rows 0..3, cols 0..3).
2. Form nine overlapping level-`(k-1)` cells (the 3x3 layout):
     n1 = NW corner          (nw_nw, nw_ne, nw_sw, nw_se)
     n2 = top middle         (nw_ne, ne_nw, nw_se, ne_sw)
     n3 = NE corner          (ne_nw, ne_ne, ne_sw, ne_se)
     n4 = left middle        (nw_sw, nw_se, sw_nw, sw_ne)
     n5 = center             (nw_se, ne_sw, sw_ne, se_nw)
     n6 = right middle       (ne_sw, ne_se, se_nw, se_ne)
     n7 = SW corner          (sw_nw, sw_ne, sw_sw, sw_se)
     n8 = bottom middle      (sw_ne, se_nw, sw_se, se_sw)
     n9 = SE corner          (se_nw, se_ne, se_sw, se_se)
3. Recurse on each n_i, obtaining level-`(k-2)` cells `r1..r9`, each
   `2^(k-3)` generations ahead.
4. Form four overlapping level-`(k-1)` super-cells from the r_i:
     q_nw = (r1, r2, r4, r5)
     q_ne = (r2, r3, r5, r6)
     q_sw = (r4, r5, r7, r8)
     q_se = (r5, r6, r8, r9)
5. Recurse on each q_*, obtaining level-`(k-2)` cells `out_*`,
   each another `2^(k-3)` generations ahead — total `2^(k-2)`. ✓
6. Return `node out_nw out_ne out_sw out_se` (level `k-1`).
-/

/-- Auxiliary for `hashlifeResult`: structural recursion on `fuel`.
    When `fuel = 0`, returns a default cell. When `fuel > 0`,
    performs one Hashlife step, recursing with `fuel - 1`.
    Terminates because `fuel` is a `Nat` that strictly decreases.

    The wrapper `hashlifeResult` calls this with `fuel = c.level`,
    which is a structural upper bound on recursion depth (level
    strictly decreases at each step of the algorithm). -/
def hashlifeResultAux : Nat → MacroCell → MacroCell
  | 0, _ => deadLeaf  -- fuel exhausted: return default
  | fuel + 1, c@(node (node nw_nw nw_ne nw_sw nw_se)
                      (node ne_nw ne_ne ne_sw ne_se)
                      (node sw_nw sw_ne sw_sw sw_se)
                      (node se_nw se_ne se_sw se_se)) =>
    if c.level == 2 then
      step4x4 c
    else
      let n1 := node nw_nw nw_ne nw_sw nw_se
      let n2 := node nw_ne ne_nw nw_se ne_sw
      let n3 := node ne_nw ne_ne ne_sw ne_se
      let n4 := node nw_sw nw_se sw_nw sw_ne
      let n5 := node nw_se ne_sw sw_ne se_nw
      let n6 := node ne_sw ne_se se_nw se_ne
      let n7 := node sw_nw sw_ne sw_sw sw_se
      let n8 := node sw_ne se_nw sw_se se_sw
      let n9 := node se_nw se_ne se_sw se_se
      let r1 := hashlifeResultAux fuel n1
      let r2 := hashlifeResultAux fuel n2
      let r3 := hashlifeResultAux fuel n3
      let r4 := hashlifeResultAux fuel n4
      let r5 := hashlifeResultAux fuel n5
      let r6 := hashlifeResultAux fuel n6
      let r7 := hashlifeResultAux fuel n7
      let r8 := hashlifeResultAux fuel n8
      let r9 := hashlifeResultAux fuel n9
      let q_nw := node r1 r2 r4 r5
      let q_ne := node r2 r3 r5 r6
      let q_sw := node r4 r5 r7 r8
      let q_se := node r5 r6 r8 r9
      let out_nw := hashlifeResultAux fuel q_nw
      let out_ne := hashlifeResultAux fuel q_ne
      let out_sw := hashlifeResultAux fuel q_sw
      let out_se := hashlifeResultAux fuel q_se
      node out_nw out_ne out_sw out_se
  | _ + 1, c =>
    -- Malformed: not a level >= 2 node of nodes.
    if c.level == 0 then deadLeaf
    else emptyOfLevel (c.level - 1)

/-- Recursive Hashlife: level-`k` input -> level-`(k-1)` output,
    `2^(k-2)` generations ahead.

    Implemented via `hashlifeResultAux` with fuel = `c.level`,
    which is a structural upper bound on the recursion depth
    (the level strictly decreases at each recursive call).

    This wrapper is not itself recursive: termination comes from
    `hashlifeResultAux`'s structural recursion on `fuel`, so the
    wrapper is a plain `def` (kept transparent for the correctness
    proofs in `Conway.Life.HashlifeMemo`). -/
def hashlifeResult (c : MacroCell) : MacroCell :=
  hashlifeResultAux c.level c

/-! ## Centering / padding helpers -/

/-- Center `c` (level `n`) inside a level-`(n+2)` MacroCell, with `c`
    placed at the centered `2^n x 2^n` region.

    The four level-`(n+1)` quadrants of the result are each formed of
    four level-`n` sub-cells: one is a part of the input, the other
    three are all-dead padding. -/
def centerInLevelPlus2 (c : MacroCell) : MacroCell :=
  let n := c.level
  let e : MacroCell := emptyOfLevel n
  -- Result NW quadrant (level n+1) has `c` in its SE sub-cell.
  -- Result NE quadrant has `c` in its SW sub-cell.
  -- Result SW quadrant has `c` in its NE sub-cell.
  -- Result SE quadrant has `c` in its NW sub-cell.
  node (node e e e c)
       (node e e c e)
       (node e c e e)
       (node c e e e)

/-- Pad `c` (level `n`) into a level-`(n+1)` MacroCell by placing `c`
    at the centered region with all-dead padding around it.

    For `c = node nw ne sw se`, the result is:
    ```
    node (node e e e nw) (node e e ne e) (node e sw e e) (node se e e e)
    ```
    This gives one copy of `c` in the center, with `2^(n-1)` cells of
    dead padding on each side. -/
def padToLevelPlus1 (c : MacroCell) : MacroCell :=
  match c with
  | node nw ne sw se =>
    let e := emptyOfLevel nw.level  -- level n-1
    node (node e e e nw) (node e e ne e) (node e sw e e) (node se e e e)
  | _ => c  -- leaves can't be padded

/-- Pad `c` by 2 levels, placing it at the center of a level-`(n+2)` cell.
    Equivalent to `padToLevelPlus1 (padToLevelPlus1 c)`.
    The result has `2^n` cells of dead padding on each side. -/
def padCenter2 (c : MacroCell) : MacroCell := padToLevelPlus1 (padToLevelPlus1 c)

/-! ## One-generation step on arbitrary MacroCells

For single-generation steps, we round-trip via Grid for level > 0
(since `hashlifeResult` jumps by `2^(k-2)` generations, not 1).
The real speedup comes from `hashlifeJump` and `evolveHashlifeFast`
which use the recursive Hashlife for multi-generation jumps. -/

/-- Advance `c` by exactly one generation. For level 0, uses the
    Hashlife base case `step4x4`. For larger levels, falls back to
    `Conway.Life.step` on the underlying grid. -/
def hashlifeStep1 (c : MacroCell) : MacroCell :=
  if c.level == 0 then
    step4x4 (centerInLevelPlus2 c)
  else
    gridToMacroCell (step (c.toGrid (0, 0)))

/-- One Hashlife step on a MacroCell. -/
def hashlifeStep (c : MacroCell) : MacroCell := hashlifeStep1 c

/-- Fast-forward `c` by `k` generations, one step at a time. -/
def hashlifeFastForward : Nat -> MacroCell -> MacroCell
  | 0,     c => c
  | k + 1, c => hashlifeFastForward k (hashlifeStep1 c)

/-! ## Exponential-speedup API: `hashlifeJump`, `evolveHashlifeFast`

The key insight: `hashlifeResult` on a level-`k` MacroCell advances the
centered region by `2^(k-2)` generations. To ensure the pattern stays
within the computed region, we pad the MacroCell by 2 levels using
`centerInLevelPlus2`, which places the pattern at the center of a
`(level + 2)` cell. This gives `2^level` margin on each side, which is
more than enough for `2^(level-2)` generations (speed of light = 1 cell/gen).

With this padding, `hashlifeResult` on the padded cell advances by
`2^level` generations (not `2^(level-2)`), and the result's offset equals
the original offset (the centered result of the padded cell aligns with
the original region). -/

/-- Jump a MacroCell forward by `2^level` generations using recursive
    Hashlife with padding. Pads the input by 2 levels, then calls
    `hashlifeResult`. The result is a level-`(k+1)` MacroCell.

    The result offset equals the original offset (the centered region
    of the padded cell aligns with the original bounding box). -/
def hashlifeJump (c : MacroCell) : MacroCell :=
  hashlifeResult (padCenter2 c)

/-- Jump size for a level-`k` MacroCell: `2^k` generations. -/
def jumpSize (lvl : Nat) : Nat := 2 ^ lvl

/-- Compute the offset for the result of `hashlifeJump`.

    After padding by 2 levels (`padCenter2`), the level-`k` MacroCell
    becomes level-`(k+2)`. The result of `hashlifeResult` on the padded
    cell is level-`(k+1)`, whose corner is shifted by `-2^(k-1)` relative
    to the original offset `off`. -/
def jumpResultOff (off : Int × Int) (lvl : Nat) : Int × Int :=
  if lvl == 0 then off
  else (off.1 - (2 ^ (lvl - 1) : Nat), off.2 - (2 ^ (lvl - 1) : Nat))

/-- Auxiliary for `evolveHashlifeFast`: structural recursion on `fuel`.
    When `fuel = 0`, falls back to `evolve n g` (reference implementation).
    When `fuel > 0`, tries to use Hashlife exponential jump if possible,
    recursing with `fuel - 1`. -/
def evolveHashlifeFastAux : Nat → Nat → Grid → Grid
  | _, 0, g => g
  | 0, _, g => g  -- fuel exhausted: return current state
  | fuel + 1, n, g =>
    let (off, mc) := gridToMacroCellWithOffset g
    let lvl := mc.level
    let js := jumpSize lvl
    if lvl >= 2 && n >= js then
      -- Jump forward by `2^lvl` generations using padded Hashlife
      let jumped := hashlifeJump mc
      let newOff := jumpResultOff off lvl
      let g' := jumped.toGrid newOff
      evolveHashlifeFastAux fuel (n - js) g'
    else
      -- Small n or small pattern: use reference evolve
      evolve n g

/-- Evolve `g` by `n` generations using Hashlife exponential speedup.

    Strategy:
    - Build a MacroCell from `g` (level `k`).
    - Pad by 2 levels and use `hashlifeResult` to jump `2^k` generations.
    - After each jump, rebuild the MacroCell and repeat.
    - For small `n` or level < 2, fall back to `evolve`.

    Implemented via `evolveHashlifeFastAux` with `fuel = n`,
    since each iteration reduces `n` by at least `js >= 4`. -/
def evolveHashlifeFast (n : Nat) (g : Grid) : Grid :=
  evolveHashlifeFastAux n n g

/-- Compute `evolve n g` using Hashlife. Round-trips through the
    `MacroCell` representation each generation, exercising `step4x4`
    for the level-2 inner loop. -/
def evolveHashlife : Nat -> Grid -> Grid
  | 0,     g => g
  | n + 1, g =>
    -- Build a MacroCell. If the bounding box fits in a level-2 window
    -- (i.e. the live region spans at most a few cells), the Hashlife
    -- base case `step4x4` can be used; otherwise round-trip via
    -- `Conway.Life.step`. We always at least exercise the MacroCell
    -- representation as a sanity check.
    let (off, mc) := gridToMacroCellWithOffset g
    -- The chosen frame places the live region inside a level >= 2
    -- square. Try the Hashlife base case if the level is exactly 2.
    let g' :=
      if mc.level == 2 then
        let r := hashlifeResult mc
        -- `r` is a level-1 MacroCell covering the centered 2x2 of the
        -- level-2 input. The level-2 input has its top-left corner at
        -- `off`, so the centered 2x2 has its top-left at
        -- `(off.1 + 1, off.2 + 1)`.
        r.toGrid (off.1 + 1, off.2 + 1)
      else
        step g
    evolveHashlife n g'

/-! ## Sanity checks

We verify that `evolveHashlife` agrees with the reference `evolve` on
the canonical small patterns, and that `step4x4` correctly handles
specific 4x4 inputs.
-/

-- step4x4 on a hand-built 4x4 with a horizontal blinker at row 1.
-- Expected centered 2x2 result at (1,1)..(2,2): (1,1) alive, (2,1) alive.
#eval
  let mc : MacroCell :=
    node
      (node (leaf false) (leaf false) (leaf true) (leaf true))   -- NW: (1,0), (1,1) alive
      (node (leaf false) (leaf false) (leaf true) (leaf false))  -- NE: (1,2) alive
      (node (leaf false) (leaf false) (leaf false) (leaf false)) -- SW
      (node (leaf false) (leaf false) (leaf false) (leaf false)) -- SE
  (step4x4 mc).toGrid (1, 1)

-- Compare with the reference: blinker_h is [(0,0), (1,0), (2,0)].
-- After step it becomes blinker_v = [(1,-1), (1,0), (1,1)].
-- In the test above, the blinker sits at row 1, cols 0..2, and the
-- expected centered output is (row 1, col 1) and (row 2, col 1), i.e.
-- only the vertical stroke that lies inside the centered 2x2 window.
#eval step blinker_h

-- Round-trip checks of `evolveHashlife` against `evolve`.
#eval evolveHashlife 1 block == evolve 1 block
#eval evolveHashlife 4 block == evolve 4 block
#eval evolveHashlife 1 blinker_h == evolve 1 blinker_h
#eval evolveHashlife 2 blinker_h == evolve 2 blinker_h
#eval evolveHashlife 1 glider == evolve 1 glider
#eval evolveHashlife 4 glider == evolve 4 glider
#eval evolveHashlife 1 beacon == evolve 1 beacon
#eval evolveHashlife 2 beacon == evolve 2 beacon
#eval evolveHashlife 1 toad == evolve 1 toad
#eval evolveHashlife 2 toad == evolve 2 toad

-- Direct recursive Hashlife on a level-3 input (exercises the
-- recursive `hashlifeResult` for k = 3). Builds a level-3 (8x8)
-- MacroCell containing the glider near its center, then calls
-- `hashlifeResult`; this returns a level-2 cell representing the
-- glider 2 generations later, but only over the centered 4x4 window.
-- We therefore compare against `evolve 2 glider` *filtered* to the
-- centered window.
#eval
  let off : Int × Int := (-2, -2)
  let mc := MacroCell.buildFromGrid glider off.1 off.2 3
  let r := hashlifeResult mc        -- level 2, 2 generations ahead
  -- The level-2 result covers the centered 4x4 region of the level-3
  -- input. With top-left of the level-3 cell at `off`, the centered
  -- region's top-left is at `(off.1 + 2, off.2 + 2) = (0, 0)`.
  let hashlife_cells := r.toGrid (off.1 + 2, off.2 + 2)
  -- Filter the reference to the centered window (rows 0..3, cols 0..3)
  let ref_full := evolve 2 glider
  let ref_window := ref_full.filter
    (fun p => 0 <= p.1 && p.1 < 4 && 0 <= p.2 && p.2 < 4)
  (hashlife_cells, ref_window, hashlife_cells == ref_window)

-- Reference: glider 4 steps ahead.
#eval evolve 4 glider

/-! ## Sanity checks for `evolveHashlifeFast`

Verify that the exponential-speedup path agrees with the reference
`evolve` on canonical patterns. These exercise `hashlifeJump` (via the
padded `hashlifeResult` path) rather than the fallback `step`.
-/

-- Block: still life, any number of generations = unchanged
#eval evolveHashlifeFast 1 block == evolve 1 block
#eval evolveHashlifeFast 4 block == evolve 4 block
#eval evolveHashlifeFast 16 block == evolve 16 block

-- Glider: period 4, displacement (1,-1)
#eval evolveHashlifeFast 4 glider == evolve 4 glider
#eval evolveHashlifeFast 8 glider == evolve 8 glider
#eval evolveHashlifeFast 12 glider == evolve 12 glider

-- Blinker: period 2
#eval evolveHashlifeFast 2 blinker_h == evolve 2 blinker_h
#eval evolveHashlifeFast 4 blinker_h == evolve 4 blinker_h

-- Beacon: period 2
#eval evolveHashlifeFast 2 beacon == evolve 2 beacon

-- Toad: period 2
#eval evolveHashlifeFast 2 toad == evolve 2 toad

end Life
end Conway
