/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway's Game of Life — toroidal engine (the tiled reading)

`Conway.Life` simulates Life on a **borderless** sparse grid: an isolated cell
evolves as on the infinite plane, and nothing ever comes back through the edge.

Not every "pillar" pattern of `Conway.Life.Pillars` is read that way, though.
The UnitCell period (`p5760unitlifecell.rle`) is real, but it belongs to the
**tiled** reading: measured on a 500 x 500 **torus**, the first repetition falls
at generations 11,324 and 5,564, i.e. a period of **5,760**. Formalising it
required a toroidal engine — absent from the lake until this module, and named
by the `Pillars.lean` docstring as the next step of that tranche.

This module provides that engine, together with the fact that makes it useful:
the **boundary model changes the fate of a pattern**.

| Pattern                        | Plane (`Conway.Life.evolve`) | 3 x 3 torus            |
|--------------------------------|------------------------------|------------------------|
| blinker `[(0,0),(1,0),(2,0)]`  | period **2**                 | saturates, then **dies** |

The very same set of three live cells is an eternal oscillator on the plane and
a dead configuration after two generations on the 3 x 3 torus: the seam makes
cells meet neighbours the plane never gives them. That is exactly what made the
UnitCell period inexpressible without tiling.

### Why `Nat` coordinates here

The toroidal engine enumerates the `h x w` cells of the box, so its coordinates
are **bounded**. They are kept in `Nat` for a kernel reason: `decide` runs the
proof in the kernel reducer, which does not reduce `List.range` (well-founded
recursion) or `Int.emod` reliably — both traps are already documented in this
lake (`List.mergeSort` "stays stuck", cf. `Conway.Life.sortDedup`). The
enumeration below is therefore **structural** (`rangeUp`), and the toroidal fold
goes through `tpred`/`tsucc` rather than a modulo.

### i18n convention (EPIC #4980, user decision 2026-07-04)

This file is the **EN sibling** of `Torus.lean` (FR canonical). The two files
differ only in their docstrings: statements, proofs and tactics are identical
— no inline bilingual block in a single file (Option B rejected).
-/

import Conway.Life

namespace Conway_en
open Conway
namespace Life_en
open Life
namespace Torus_en

/-! ## Toroidal wrap of one coordinate

The wrap is a conditional step, not a modulo: `tpred` and `tsucc` are `if`
clauses over natural numbers, so the kernel reduces them without effort.
-/

/-- Toroidal predecessor in `[0, n)`: `0` has predecessor `n - 1`. -/
def tpred (n : Nat) (i : Nat) : Nat := if i = 0 then n - 1 else i - 1

/-- Toroidal successor in `[0, n)`: `n - 1` has successor `0`. -/
def tsucc (n : Nat) (i : Nat) : Nat := if i + 1 = n then 0 else i + 1

/-- `[0, n)` in increasing order, by **structural** recursion on `n`.

    `List.range` builds the same list by well-founded recursion, which the
    kernel reducer does not unfold; `rangeUp` is the version `decide` can
    evaluate. -/
def rangeUp : Nat → List Nat
  | 0 => []
  | n + 1 => rangeUp n ++ [n]

/-- The `h x w` cells of the torus, in increasing order (row then column).

    The increasing order is what makes the witnesses readable: `torusStep`
    filters that list without reordering it, so its outputs are canonical just
    like those of `Conway.Life.step` (which sorts and deduplicates). -/
def torusCells (h w : Nat) : List (Nat × Nat) :=
  (rangeUp h).flatMap (fun r => (rangeUp w).map (fun c => (r, c)))

/-- The eight Moore neighbours of a cell on the `h x w` torus, each
    coordinate wrapped independently, the cell itself removed. -/
def torusNeighbors (h w : Nat) (p : Nat × Nat) : List (Nat × Nat) :=
  let rs := [tpred h p.1, p.1, tsucc h p.1]
  let cs := [tpred w p.2, p.2, tsucc w p.2]
  ((rs.flatMap (fun r => cs.map (fun c => (r, c)))).filter (fun q => q != p))

/-- A cell is alive in a toroidal grid when it appears in it. -/
def torusLive (g : List (Nat × Nat)) (p : Nat × Nat) : Bool :=
  g.elem p

/-- Number of live neighbours of `p` on the torus. -/
def torusCount (h w : Nat) (g : List (Nat × Nat)) (p : Nat × Nat) : Nat :=
  (torusNeighbors h w p).countP (torusLive g)

/-- The B3/S23 rule on the torus: identical to the plane, only the neighbourhood changes. -/
def torusAliveNext (h w : Nat) (g : List (Nat × Nat)) (p : Nat × Nat) : Bool :=
  let n := torusCount h w g p
  if torusLive g p then
    n == 2 || n == 3
  else
    n == 3

/-- One generation on the `h x w` torus. -/
def torusStep (h w : Nat) (g : List (Nat × Nat)) : List (Nat × Nat) :=
  (torusCells h w).filter (fun p => torusAliveNext h w g p)

/-- `n` generations on the `h x w` torus. -/
def torusEvolve (h w : Nat) (n : Nat) (g : List (Nat × Nat)) : List (Nat × Nat) :=
  -- Parentheses are mandatory: `^[` binds tighter than application, so
  -- `torusStep h w ^[n]` would parse as `torusStep h (w ^[n])`. `Conway.Life.evolve`
  -- escapes that trap only because it iterates a bare identifier (`step^[n]`).
  (torusStep h w)^[n] g

/-- Translation of a toroidal grid: no wrap, hence injective — the list order
    is preserved and no duplicate appears. -/
def torusShift (dr dc : Nat) (g : List (Nat × Nat)) : List (Nat × Nat) :=
  g.map (fun p => (p.1 + dr, p.2 + dc))

/-! ## The torus is closed

One generation does not leave the box: every candidate cell comes from
`torusCells h w`. That is the property that separates the torus from the plane,
where cells escape indefinitely (the fact measured on the UnitCell).
-/

/-- Every cell of one generation belongs to the `h x w` box. -/
theorem torusStep_subset (h w : Nat) (g : List (Nat × Nat)) :
    ∀ p ∈ torusStep h w g, p ∈ torusCells h w := by
  intro p hp
  -- `List.mem_filter` yields `(a ∈ l) ∧ (p a = true)`: membership is the
  -- first component.
  exact (List.mem_filter.mp hp).1

/-- `torusEvolve` adds no cell outside the box either — **provided the input
    grid starts inside the box**. The proviso is not cosmetic: at `n = 0` the
    engine returns the grid as-is, so an out-of-box input would stay out of box.
    That is the price of the tiled reading: the torus is closed from the first
    generation onwards. -/
theorem torusEvolve_subset (h w : Nat) {g : List (Nat × Nat)}
    (hg : ∀ p ∈ g, p ∈ torusCells h w) (n : Nat) :
    ∀ p ∈ torusEvolve h w n g, p ∈ torusCells h w := by
  induction n with
  | zero => exact hg
  | succ k ih =>
      intro p hp
      simp only [torusEvolve, Function.iterate_succ_apply'] at hp
      exact torusStep_subset h w _ p hp

@[simp] theorem torusEvolve_zero (h w : Nat) (g : List (Nat × Nat)) :
    torusEvolve h w 0 g = g := rfl

@[simp] theorem torusEvolve_succ (h w : Nat) (n : Nat) (g : List (Nat × Nat)) :
    torusEvolve h w (n + 1) g = torusStep h w (torusEvolve h w n g) := by
  simp [torusEvolve, Function.iterate_succ_apply']

/-! ## Witnesses

All are proved by `decide` in the kernel: **no `native_decide`**, hence no new
axiom. The lake's `proof-integrity` gate reddens on any unlisted `native_decide`;
these statements add none.
-/

/-- The lake's horizontal blinker, restated for the readability of the statements. -/
def blinkerT : List (Nat × Nat) := [(0, 0), (1, 0), (2, 0)]

/-- The same blinker, translated so it sits entirely away from the seams of a
    5 x 5 torus (rows 1..3, column 2 — no coordinate on the border). -/
def blinkerT5 : List (Nat × Nat) := [(1, 2), (2, 2), (3, 2)]

/-- The standard glider, five cells, in increasing order. -/
def gliderT : List (Nat × Nat) := [(0, 2), (1, 0), (1, 2), (2, 1), (2, 2)]

/-- **The blinker has period 2 on the plane.** A statement absent from the lake
    as a theorem: it only appeared as a commented `#eval` (`Hashlife.lean`). -/
theorem blinker_plane_period_two : evolve 2 blinker_h = blinker_h := by decide

/-- **Paired negative witness**: the plane blinker is not a still life, so its
    period is 2 and not 1. -/
theorem blinker_plane_not_still : evolve 1 blinker_h ≠ blinker_h := by decide

/-- **Torus / plane agreement away from the seam.** On a 5 x 5 torus, a blinker
    that touches no seam has the same period 2 as on the plane: the toroidal
    engine does not distort what it does not need to fold. -/
theorem blinker_torus5_period_two :
    torusEvolve 5 5 2 blinkerT5 = blinkerT5 := by decide

/-- **Paired negative witness**: period 2, not 1. -/
theorem blinker_torus5_not_still :
    torusEvolve 5 5 1 blinkerT5 ≠ blinkerT5 := by decide

/-- **The divergence of boundary models.** The same row of three aligned cells,
    placed on a 3 x 3 torus, saturates the box in one generation. -/
theorem blinker_torus3_saturates :
    torusEvolve 3 3 1 blinkerT = torusCells 3 3 := by decide

/-- **... then dies**: two generations are enough to empty the grid, whereas the
    same pattern oscillates forever on the plane (`blinker_plane_period_two`).
    This is the witness that explains why the UnitCell period was not expressible
    without tiling. -/
theorem blinker_torus3_dies :
    torusEvolve 3 3 2 blinkerT = [] := by decide

/-- **Paired negative witness**: the grid is not already empty after a single
    generation — the extinction is indeed an effect of the second one. -/
theorem blinker_torus3_not_dead_at_one :
    torusEvolve 3 3 1 blinkerT ≠ [] := by decide

/-- **A spaceship on the torus**: the glider, after four generations on a
    20 x 20 torus, is the `(1, 1)` translate of itself. The fold does not hinder
    its flight as long as it does not reach the seam. -/
theorem glider_torus_spaceship :
    torusEvolve 20 20 4 gliderT = torusShift 1 1 gliderT := by decide

/-- **Paired negative witness**: the glider is not motionless — its period is
    therefore not 1. -/
theorem glider_torus_not_still :
    torusEvolve 20 20 1 gliderT ≠ gliderT := by decide

end Torus_en
end Life_en
end Conway_en
