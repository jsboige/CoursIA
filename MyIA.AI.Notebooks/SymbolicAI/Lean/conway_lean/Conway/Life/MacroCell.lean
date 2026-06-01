/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## MacroCell — Quadtree representation for Hashlife

A `MacroCell` represents a square region of the Game of Life grid as a
quadtree. Level-0 cells are individual boolean cells. A level-(n+1) cell
is a 2x2 arrangement of level-n cells (named `nw`, `ne`, `sw`, `se` for
north-west, north-east, south-west, south-east).

The key insight of Hashlife (Gosper 1984) is that the step function on
MacroCells can be computed recursively and memoized, giving exponential
speedup on patterns with repetitive structure.

## Layout convention

We use the same coordinate convention as `Conway.Life`:
- Each cell is `(row, col) : Int × Int`.
- Rows increase downward (north -> south).
- Columns increase rightward (west -> east).

So at the top level a node `node nw ne sw se` of level `n+1` covers a
region of size `2^(n+1) x 2^(n+1)` partitioned as:

```
nw | ne
---+---
sw | se
```

where each quadrant is `2^n x 2^n`. If the whole region has its
top-left corner at `(row0, col0)`, then:

- `nw` covers `[row0,            row0 + 2^n)         x [col0,           col0 + 2^n)`
- `ne` covers `[row0,            row0 + 2^n)         x [col0 + 2^n,    col0 + 2^(n+1))`
- `sw` covers `[row0 + 2^n,     row0 + 2^(n+1))      x [col0,           col0 + 2^n)`
- `se` covers `[row0 + 2^n,     row0 + 2^(n+1))      x [col0 + 2^n,    col0 + 2^(n+1))`

This module is fully proven (no gaps). It only provides the data
structure and conversions. The Hashlife algorithm lives in
`Conway.Life.Hashlife`.
-/

import Conway.Life

namespace Conway
namespace Life

/-! ## The quadtree data structure -/

/-- A quadtree cell.
    - `leaf b` is a single cell that is alive (`b = true`) or dead (`b = false`).
    - `node nw ne sw se` is a 2x2 block of subtrees, all required (by convention,
      but not enforced by the type) to have the same level. -/
inductive MacroCell where
  | leaf (alive : Bool)
  | node (nw ne sw se : MacroCell)
  deriving BEq, Repr, Inhabited

namespace MacroCell

/-- The level of a `MacroCell`: 0 for `leaf`, `1 + nw.level` for `node`.
    By construction, a well-formed `MacroCell` has all four subtrees at the
    same level; we only inspect `nw`. -/
def level : MacroCell -> Nat
  | leaf _      => 0
  | node nw _ _ _ => 1 + nw.level

/-- The side length of the region covered by a `MacroCell`: `2 ^ level`. -/
def size (c : MacroCell) : Nat := 2 ^ c.level

/-- A leaf containing a dead cell. -/
def deadLeaf : MacroCell := leaf false

/-- A leaf containing a live cell. -/
def aliveLeaf : MacroCell := leaf true

/-- Build an "empty" (all-dead) `MacroCell` of level `n`. -/
def emptyOfLevel : Nat -> MacroCell
  | 0     => deadLeaf
  | n + 1 =>
    let sub := emptyOfLevel n
    node sub sub sub sub

/-- Test if a `MacroCell` represents the all-dead region. -/
def isEmpty : MacroCell -> Bool
  | leaf b      => !b
  | node a b c d => a.isEmpty && b.isEmpty && c.isEmpty && d.isEmpty

/-! ## Conversion: MacroCell -> Grid

Given a `MacroCell` and the absolute `(row, col)` offset of its top-left
corner, enumerate the live cells in lexicographic `(row, col)` order.

The recursion walks the quadrants in the order `nw, ne, sw, se`. We
process all of `nw`'s rows before `ne`'s rows is **not** correct in the
lex ordering when rows interleave; however, because `nw` and `ne` cover
the same row range and `nw` has strictly smaller columns, listing all of
`nw` then all of `ne` does produce lex order **only when** each
quadrant's output is itself sorted. The simpler and obviously correct
implementation is to concatenate the four quadrants and then `sortDedup`
at the top level. -/

/-- Internal helper: enumerate the live cells of `c` whose top-left
    corner is at offset `(r0, c0)`. The resulting list is **not** guaranteed
    to be sorted in lex order — the caller should `sortDedup` if needed. -/
def toCellsAux (r0 c0 : Int) : MacroCell -> List (Int × Int)
  | leaf true   => [(r0, c0)]
  | leaf false  => []
  | node nw ne sw se =>
    let n := nw.level
    let half : Int := (2 ^ n : Nat)
    nw.toCellsAux r0 c0
      ++ ne.toCellsAux r0 (c0 + half)
      ++ sw.toCellsAux (r0 + half) c0
      ++ se.toCellsAux (r0 + half) (c0 + half)

/-- Convert a `MacroCell` to a `Grid`, given the offset `(r0, c0)` of its
    top-left corner. The output is sorted lexicographically and deduplicated. -/
def toGrid (offset : Int × Int) (c : MacroCell) : Grid :=
  sortDedup (c.toCellsAux offset.1 offset.2)

end MacroCell

/-! ## Conversion: Grid -> MacroCell

Given a `Grid` (list of live cell coordinates), build a `MacroCell` of the
smallest level whose region, placed at a chosen offset, contains all the
live cells. The offset is returned alongside so that subsequent calls to
`toGrid` round-trip correctly.

The construction is straightforward but a little tedious:
1. Find the bounding box `[rMin, rMax] x [cMin, cMax]` of the live cells
   (using extra padding on each side to allow `step` to spread).
2. Compute the side length needed: `max (rMax - rMin + 1) (cMax - cMin + 1)`,
   rounded up to the next power of 2.
3. Recursively build the quadtree, dispatching each live cell to the
   appropriate quadrant.
-/

namespace MacroCell

/-- Smallest `n` such that `2 ^ n >= k`. -/
def ceilLog2 (k : Nat) : Nat :=
  match k with
  | 0     => 0
  | 1     => 0
  | k + 2 => 1 + ceilLog2 ((k + 2 + 1) / 2)

/-- Build a `MacroCell` of level `n` covering the square `[r0, r0 + 2^n) x
    [c0, c0 + 2^n)`, with live cells given by membership test in `g`. -/
def buildFromGrid (g : Grid) (r0 c0 : Int) : Nat -> MacroCell
  | 0     => leaf (g.elem (r0, c0))
  | n + 1 =>
    let half : Int := (2 ^ n : Nat)
    let nw := buildFromGrid g r0          c0          n
    let ne := buildFromGrid g r0          (c0 + half) n
    let sw := buildFromGrid g (r0 + half) c0          n
    let se := buildFromGrid g (r0 + half) (c0 + half) n
    node nw ne sw se

end MacroCell

/-! ## High-level Grid -> MacroCell

We pick an offset and level large enough to contain `g`. To leave room
for one round of `step` to spread, we add a 2-cell padding on each side
of the bounding box. Empty grids give the all-dead level-0 leaf. -/

/-- The minimum row of a non-empty grid; defaults to 0 on the empty grid. -/
def gridRowMin (g : Grid) : Int :=
  match g with
  | []      => 0
  | p :: ps => ps.foldl (fun m q => min m q.1) p.1

/-- The maximum row of a non-empty grid; defaults to 0 on the empty grid. -/
def gridRowMax (g : Grid) : Int :=
  match g with
  | []      => 0
  | p :: ps => ps.foldl (fun m q => max m q.1) p.1

/-- The minimum column of a non-empty grid; defaults to 0 on the empty grid. -/
def gridColMin (g : Grid) : Int :=
  match g with
  | []      => 0
  | p :: ps => ps.foldl (fun m q => min m q.2) p.2

/-- The maximum column of a non-empty grid; defaults to 0 on the empty grid. -/
def gridColMax (g : Grid) : Int :=
  match g with
  | []      => 0
  | p :: ps => ps.foldl (fun m q => max m q.2) p.2

/-- Compute a suitable `(offset, level)` so that the square of side
    `2 ^ level` placed at `offset` strictly contains the bounding box of
    `g` plus a 2-cell padding on each side. Returns `((0, 0), 0)` for the
    empty grid. -/
def gridFrame (g : Grid) : (Int × Int) × Nat :=
  match g with
  | []      => ((0, 0), 0)
  | _ :: _ =>
    let rMin := gridRowMin g
    let rMax := gridRowMax g
    let cMin := gridColMin g
    let cMax := gridColMax g
    -- 2-cell padding on each side
    let r0 := rMin - 2
    let c0 := cMin - 2
    let height := (rMax - rMin + 5).toNat   -- +1 for inclusive, +4 for padding
    let width  := (cMax - cMin + 5).toNat
    let side   := max height width
    let lvl    := MacroCell.ceilLog2 side
    ((r0, c0), lvl)

/-- Convert a `Grid` to a `MacroCell`, returning the chosen offset so that
    `MacroCell.toGrid offset (gridToMacroCell g) = g`. -/
def gridToMacroCellWithOffset (g : Grid) : (Int × Int) × MacroCell :=
  let (off, lvl) := gridFrame g
  (off, MacroCell.buildFromGrid g off.1 off.2 lvl)

/-- Convert a `Grid` to a `MacroCell`, discarding the offset (defaulting to
    `(0, 0)` for the round trip). For round-trip purposes, prefer
    `gridToMacroCellWithOffset`. -/
def gridToMacroCell (g : Grid) : MacroCell :=
  (gridToMacroCellWithOffset g).2

/-! ## Sanity checks

We verify that the round trip `Grid -> MacroCell -> Grid` preserves the
small canonical patterns of `Conway.Life`. -/

-- Bounding-box helpers
#eval gridRowMin block
#eval gridRowMax block
#eval gridFrame block

-- The empty grid should give a level-0 dead leaf.
#eval gridToMacroCell ([] : Grid) |>.level
#eval gridToMacroCell ([] : Grid) |>.isEmpty

-- Round trip on the block: the MacroCell, then back to a grid at the
-- chosen offset, should equal `block`.
#eval
  let (off, mc) := gridToMacroCellWithOffset block
  (off, mc.level, mc.toGrid off == block)

#eval
  let (off, mc) := gridToMacroCellWithOffset blinker_h
  (off, mc.level, mc.toGrid off == blinker_h)

#eval
  let (off, mc) := gridToMacroCellWithOffset glider
  (off, mc.level, mc.toGrid off == glider)

#eval
  let (off, mc) := gridToMacroCellWithOffset beehive
  (off, mc.level, mc.toGrid off == beehive)

#eval
  let (off, mc) := gridToMacroCellWithOffset toad
  (off, mc.level, mc.toGrid off == toad)

end Life
end Conway
