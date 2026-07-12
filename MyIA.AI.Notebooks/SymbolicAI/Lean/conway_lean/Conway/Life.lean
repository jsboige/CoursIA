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
- Game state encoded as a `List (Int × Int)` of live cells (sorted, unique)
- Step function implementing the B3/S23 rule via list operations
- Iterated `evolve`
- Predicates `IsStillLife`, `IsOscillator`, `IsSpaceship`
- Witnesses for the canonical small patterns
  (block, beehive, blinker, toad, beacon, glider)
- Microproofs verifiable by `native_decide` on list equality

The list representation avoids the `Quot.lift` / `Eq.rec` bottleneck
that arises when Lean's kernel tries to decide `Finset` equality
constructed via `image`/`biUnion`/`filter` on `Int × Int`. List
equality reduces to cons-by-cons structural comparison, which the
kernel and native code generator handle efficiently.

The hashlife optimisation (Gosper 1984), the RLE parser, and the three
community pillars (Gemini, OTCA Metapixel, Carlini 8-bit computer) are
deferred to Phases 2 to 9 of Epic #1647.

This module is fully proven (no gaps).
-/

import Mathlib.Tactic

namespace Conway
namespace Life

/-! ## Basic types

We model the live cells as a sorted, deduplicated list of integer
coordinates. Dead cells are those not in the list.
-/

/-- Lexicographic ordering on `Int × Int` for sorting. -/
def lexLt (a b : Int × Int) : Bool :=
  if a.1 < b.1 then true
  else if a.1 > b.1 then false
  else a.2 < b.2

/-- A grid of Conway's Game of Life: sorted, deduplicated list of live cells.
    We use `List` rather than `Finset` because list equality is decided by
    structural comparison (no `Quot.lift`), which `native_decide` handles. -/
abbrev Grid := List (Int × Int)

/-! ## Neighborhood

The Moore (king-move) neighborhood: 8 cells surrounding a given cell.
We return them as a plain list (order does not matter for counting).
-/

/-- The 8 Moore neighbors of a cell `p`. -/
def mooreNeighbors (p : Int × Int) : List (Int × Int) :=
  [(p.1 - 1, p.2 - 1), (p.1 - 1, p.2), (p.1 - 1, p.2 + 1),
   (p.1, p.2 - 1),                 (p.1, p.2 + 1),
   (p.1 + 1, p.2 - 1), (p.1 + 1, p.2), (p.1 + 1, p.2 + 1)]

/-! ## The B3/S23 rule

For every cell, count its live Moore neighbors:
- A dead cell with exactly 3 live neighbors becomes alive (Birth = B3)
- A live cell with 2 or 3 live neighbors stays alive (Survival = S23)
- Otherwise the cell is dead
-/

/-- Check if a cell is alive in a grid (membership test). -/
def isAlive (g : Grid) (p : Int × Int) : Bool :=
  g.elem p

/-- Count the live Moore neighbors of `p` in grid `g`. -/
def liveNeighborCount (g : Grid) (p : Int × Int) : Nat :=
  (mooreNeighbors p).countP (isAlive g)

/-- The B3/S23 rule: should `p` be alive at the next generation? -/
def aliveNext (g : Grid) (p : Int × Int) : Bool :=
  let n := liveNeighborCount g p
  if isAlive g p then
    n == 2 || n == 3   -- S23
  else
    n == 3             -- B3

/-- Candidate cells for next-step: live cells and their neighbors. -/
def candidates (g : Grid) : List (Int × Int) :=
  g ++ g.flatMap mooreNeighbors

/-- Reflexive closure of `lexLt`: a **total** comparator for `mergeSort`.
    On distinct pairs it decides exactly like `lexLt`; on equal pairs it is
    `true`. Totality is what `List.pairwise_mergeSort` needs to certify that
    the output is sorted (see `Conway.Life.GridCanonical`). -/
def lexLe (a b : Int × Int) : Bool :=
  lexLt a b || a == b

/-- Sort a list lexicographically and remove duplicates.

    The comparator is the total `lexLe` and deduplication uses Mathlib's
    `List.dedup`, so the canonical-form lemmas (`sortedness`, `Nodup`,
    membership, extensionality) are all derivable — see
    `Conway.Life.GridCanonical`. The output is the same as with the strict
    comparator + `eraseDups`: the comparators agree on all distinct pairs,
    ties are *equal values* (so any tie-breaking yields the same list), and
    on a sorted list both dedup flavours collapse each run of equal values
    to a single copy. -/
def sortDedup (l : List (Int × Int)) : List (Int × Int) :=
  (l.mergeSort lexLe).dedup

/-- `sortDedup` preserves membership. -/
theorem mem_sortDedup {p : Int × Int} {l : List (Int × Int)} :
    p ∈ sortDedup l ↔ p ∈ l := by
  unfold sortDedup
  rw [List.mem_dedup, List.mem_mergeSort]

/-- One step of Conway's Game of Life (B3/S23 rule). -/
def step (g : Grid) : Grid :=
  sortDedup ((candidates g).filter (fun p => aliveNext g p))

/-- Iterated step: `evolve n g` applies `step` `n` times to `g`. -/
def evolve (n : Nat) (g : Grid) : Grid :=
  step^[n] g

@[simp] theorem evolve_zero (g : Grid) : evolve 0 g = g := rfl

@[simp] theorem evolve_succ (n : Nat) (g : Grid) :
    evolve (n + 1) g = step (evolve n g) := by
  simp [evolve, Function.iterate_succ_apply']

/-! ## Pattern predicates

We define Boolean-valued predicates (returning `Bool`) so that `native_decide`
can evaluate them by compiling to native code and comparing `Bool` equality.
No `Decidable` synthesis or `Quot.lift` needed — just `Bool` reduction.
-/

/-- A still life: a grid unchanged by one step of evolution. -/
def isStillLife (g : Grid) : Bool := step g == g

/-- A pure oscillator of period `n`: returns to itself in exactly `n` steps. -/
def isOscillator (g : Grid) (n : Nat) : Bool := evolve n g == g

/-- Translate every cell of a grid by a fixed displacement `v`. -/
def shift (v : Int × Int) (g : Grid) : Grid :=
  sortDedup (g.map (fun p => (p.1 + v.1, p.2 + v.2)))

/-- A spaceship of period `n` and displacement `v`: after `n` steps the
    pattern reappears, translated by `v`. -/
def isSpaceship (g : Grid) (n : Nat) (v : Int × Int) : Bool :=
  evolve n g == shift v g

/-! ## Canonical patterns

These are the most famous small patterns of Conway's Game of Life,
discovered in the early 1970s by Conway's group at Cambridge and by
players of the M.I.T. PDP-6/PDP-10 community.

Each pattern is given in sorted lexicographic order so that `step`
produces a list in the same order, enabling `native_decide` to verify
equality by structural comparison.
-/

/-- The **Block**: a 2x2 square. The smallest still life. -/
def block : Grid := [(0, 0), (0, 1), (1, 0), (1, 1)]

/-- The **Beehive**: a 6-cell hexagonal still life. -/
def beehive : Grid := [(0, 1), (1, 0), (1, 2), (2, 0), (2, 2), (3, 1)]

/-- The **Blinker** (horizontal): three cells in a row. Period-2 oscillator. -/
def blinker_h : Grid := [(0, 0), (1, 0), (2, 0)]

/-- The **Blinker** (vertical): three cells in a column. -/
def blinker_v : Grid := [(1, -1), (1, 0), (1, 1)]

/-- The **Toad** (phase 1): a period-2 oscillator. -/
def toad : Grid := [(0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0)]

/-- The **Beacon** (phase 1): two blocks touching diagonally. Period 2. -/
def beacon : Grid :=
  [(0, 0), (0, 1), (1, 0), (1, 1), (2, 2), (2, 3), (3, 2), (3, 3)]

/-- The **Glider** (phase 1, south-east bound): the smallest spaceship.
    After 4 generations it reappears, translated by (1, -1). -/
def glider : Grid := [(0, 0), (1, 0), (1, 2), (2, 0), (2, 1)]

/-! ## Microproofs

These are the first formal results of Phase 1: simple verifications of
classic patterns by `native_decide`. The predicates return `Bool`, so
`native_decide` compiles the step function to native code, evaluates the
Boolean expression, and checks it equals `true`. No `Decidable` synthesis
or `Quot.lift` involved.
-/

/-- The Block is a still life: `isStillLife block = true`. -/
theorem block_still_life : isStillLife block = true := by native_decide

/-- The Beehive is a still life. -/
theorem beehive_still_life : isStillLife beehive = true := by native_decide

/-- The horizontal Blinker oscillates with period 2. -/
theorem blinker_period_two : isOscillator blinker_h 2 = true := by native_decide

/-- One step turns the horizontal Blinker into the vertical Blinker. -/
theorem blinker_step : (step blinker_h == blinker_v) = true := by native_decide

/-- The Toad oscillates with period 2. -/
theorem toad_period_two : isOscillator toad 2 = true := by native_decide

/-- The Beacon oscillates with period 2. -/
theorem beacon_period_two : isOscillator beacon 2 = true := by native_decide

/-- The Glider is a spaceship of period 4, displacement `(1, -1)`. -/
theorem glider_spaceship : isSpaceship glider 4 (1, -1) = true := by native_decide

end Life
end Conway
