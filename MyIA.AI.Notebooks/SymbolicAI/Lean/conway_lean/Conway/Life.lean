/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway's Game of Life — Phase 1 foundations

John Horton Conway (1937-2020) invented the Game of Life in 1970 in
collaboration with the Cambridge graduate students Michael Guy and others.
A cellular automaton on the integer plane with the celebrated B3/S23 rule.
Despite extreme simplicity, the rule supports universal computation
(Conway 1982; Rendell 2000) and self-replication (Wade 2010 — Gemini).

This file is the FOUNDATIONS module of the Phase 2 tribute (Epic #1647):
- Game state encoded as a `Finset (Int × Int)` of live cells
- Step function implementing the B3/S23 rule
- Iterated `evolve`
- Predicates `IsStillLife`, `IsOscillator`, `IsSpaceship`
- Witnesses for the canonical small patterns
  (block, beehive, blinker, toad, beacon, glider)
- Microproofs verifiable by `native_decide` on the discretised support

The hashlife optimisation (Gosper 1984), the RLE parser, and the three
community pillars (Gemini, OTCA Metapixel, Carlini 8-bit computer) are
deferred to Phases 2 to 9 of Epic #1647.

This module is fully proven (no gaps).
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Logic.Function.Iterate

namespace Conway
namespace Life

/-! ## Basic types

We model the live cells as a finite set of integer coordinates.
Dead cells are simply those not in the set. This is the standard
"sparse" representation, used by Golly, lifelib, and most simulators.
-/

/-- A grid of Conway's Game of Life: the finite set of live cells. -/
abbrev Grid := Finset (Int × Int)

/-! ## Neighborhood

The Moore (king-move) neighborhood: 8 cells surrounding a given cell.
-/

/-- The 8 Moore neighbors of a cell `p`. -/
def neighbors (p : Int × Int) : Finset (Int × Int) :=
  (({-1, 0, 1} : Finset Int) ×ˢ ({-1, 0, 1} : Finset Int)).image
    (fun d => (p.1 + d.1, p.2 + d.2)) |>.erase p

/-- Sanity: a Moore neighborhood has exactly 8 cells. -/
theorem neighbors_card (p : Int × Int) : (neighbors p).card = 8 := by
  native_decide

/-! ## The B3/S23 rule

For every cell, count its live Moore neighbors:
- A dead cell with exactly 3 live neighbors becomes alive (Birth = B3)
- A live cell with 2 or 3 live neighbors stays alive (Survival = S23)
- Otherwise the cell is dead

We implement this by iterating over the bounding box (live cells and their
neighbors) and selecting those that survive or are born.
-/

/-- Count the live Moore neighbors of `p` in grid `g`. -/
def liveNeighborCount (g : Grid) (p : Int × Int) : Nat :=
  (neighbors p ∩ g).card

/-- The B3/S23 rule: should `p` be alive at the next generation? -/
def aliveNext (g : Grid) (p : Int × Int) : Bool :=
  let n := liveNeighborCount g p
  if p ∈ g then
    decide (n = 2 ∨ n = 3)   -- S23
  else
    decide (n = 3)           -- B3

/-- Candidate cells for next-step survival: live cells and their neighbors.
    No new cell can be born outside this bounding zone (B3 requires 3 live
    neighbors among the 8 Moore neighbors of a dead cell). -/
def candidates (g : Grid) : Finset (Int × Int) :=
  g ∪ g.biUnion neighbors

/-- One step of Conway's Game of Life (B3/S23 rule). -/
def step (g : Grid) : Grid :=
  (candidates g).filter (aliveNext g)

/-- Iterated step: `evolve n g` applies `step` `n` times to `g`. -/
def evolve (n : Nat) (g : Grid) : Grid :=
  step^[n] g

@[simp] theorem evolve_zero (g : Grid) : evolve 0 g = g := rfl

@[simp] theorem evolve_succ (n : Nat) (g : Grid) :
    evolve (n + 1) g = step (evolve n g) := by
  simp [evolve, Function.iterate_succ', Function.comp]

/-! ## Pattern predicates -/

/-- A still life: a grid unchanged by one step of evolution.
    The simplest non-trivial fixed points of `step`. -/
def IsStillLife (g : Grid) : Prop := step g = g

instance (g : Grid) : Decidable (IsStillLife g) :=
  inferInstanceAs (Decidable (step g = g))

/-- A pure oscillator of period `n`: returns to itself in exactly `n` steps. -/
def IsOscillator (g : Grid) (n : Nat) : Prop := evolve n g = g

instance (g : Grid) (n : Nat) : Decidable (IsOscillator g n) :=
  inferInstanceAs (Decidable (evolve n g = g))

/-- Translate every cell of a grid by a fixed displacement `v`. -/
def shift (v : Int × Int) (g : Grid) : Grid :=
  g.image (fun p => (p.1 + v.1, p.2 + v.2))

/-- A spaceship of period `n` and displacement `v`: after `n` steps the
    pattern reappears, translated by `v`. (`v = (0, 0)` recovers oscillators.) -/
def IsSpaceship (g : Grid) (n : Nat) (v : Int × Int) : Prop :=
  evolve n g = shift v g

instance (g : Grid) (n : Nat) (v : Int × Int) :
    Decidable (IsSpaceship g n v) :=
  inferInstanceAs (Decidable (evolve n g = shift v g))

/-! ## Canonical patterns

These are the most famous small patterns of Conway's Game of Life,
discovered in the early 1970s by Conway's group at Cambridge and by
players of the M.I.T. PDP-6/PDP-10 community.
-/

/-- The **Block**: a 2×2 square. The smallest still life. -/
def block : Grid := {(0, 0), (0, 1), (1, 0), (1, 1)}

/-- The **Beehive**: a 6-cell hexagonal still life. -/
def beehive : Grid :=
  {(1, 0), (2, 0), (0, 1), (3, 1), (1, 2), (2, 2)}

/-- The **Blinker** (horizontal): three cells in a row. Period-2 oscillator. -/
def blinker_h : Grid := {(0, 0), (1, 0), (2, 0)}

/-- The **Blinker** (vertical): three cells in a column. -/
def blinker_v : Grid := {(1, -1), (1, 0), (1, 1)}

/-- The **Toad** (phase 1): a period-2 oscillator. -/
def toad : Grid :=
  {(1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (2, 1)}

/-- The **Beacon** (phase 1): two blocks touching diagonally. Period 2. -/
def beacon : Grid :=
  {(0, 0), (1, 0), (0, 1), (1, 1),
   (2, 2), (3, 2), (2, 3), (3, 3)}

/-- The **Glider** (phase 1, south-east bound): the smallest spaceship.
    After 4 generations it reappears, translated by (1, -1). -/
def glider : Grid :=
  {(0, 0), (1, 0), (2, 0), (2, 1), (1, 2)}

/-! ## Microproofs

These are the first formal results of Phase 1: simple verifications of
classic patterns by `native_decide`. Each one is a finite computation
on small `Finset (Int × Int)` and exercises every layer of the model
(`step`, `evolve`, `shift`, the three predicates).
-/

/-- The Block is a still life: `step block = block`. -/
theorem block_still_life : IsStillLife block := by native_decide

/-- The Beehive is a still life. -/
theorem beehive_still_life : IsStillLife beehive := by native_decide

/-- The horizontal Blinker oscillates with period 2. -/
theorem blinker_period_two : IsOscillator blinker_h 2 := by native_decide

/-- One step turns the horizontal Blinker into the vertical Blinker. -/
theorem blinker_step : step blinker_h = blinker_v := by native_decide

/-- The Toad oscillates with period 2. -/
theorem toad_period_two : IsOscillator toad 2 := by native_decide

/-- The Beacon oscillates with period 2. -/
theorem beacon_period_two : IsOscillator beacon 2 := by native_decide

/-- The Glider is a spaceship of period 4, displacement `(1, -1)`. -/
theorem glider_spaceship : IsSpaceship glider 4 (1, -1) := by native_decide

end Life
end Conway
