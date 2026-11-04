/-
Copyright (c) 2026 CoursIA. All rights reserved.
Distributed under the Apache 2.0 License as described in the LICENSE file.

## Decidability map of the G2 gate (centralCorrect) over the bestiary

Companion crible module to `Conway.Life.AdversarialBattery_en` (the public
MacroCell witness bestiary, #9589) and `Conway.Life.HashlifeCorrectness` (the G2
infrastructure `centralCorrect` / `centralCorrect_mem`, c.153). It maps firsthand,
by `decide`, **which parts of the G2 gate are kernel-decidable**, and honestly
documents the part that is not.

### Motivation — the structure of the G2 gate

The G2 gate (`centralCorrect_mem`, HashlifeCorrectness L2410) characterizes the
pointwise membership of the hashlife result **without reducing `hashlifeResultAux`**
(this is the whnf-wall bypass by congruence, c.153):

  `p ∈ (hashlifeResultAux (j+2) c).toGrid (2^j, 2^j) ↔
     isAlive (evolve (2^j) (c.toGrid (0, 0))) p = true ∧
     (2^j : Int) ≤ p.1 ∧ p.1 < (2^j : Int) + 2^(j+1) ∧
     (2^j : Int) ≤ p.2 ∧ p.2 < (2^j : Int) + 2^(j+1)`

under hypothesis `h : centralCorrect c j`. The gate thus decomposes into THREE
ingredients: (H) the hypothesis `centralCorrect` itself, (A) the "alive" side
`isAlive (evolve ...)`, (B) the "bounds" side `[2^j, 2^j + 2^(j+1))`. The
decidability question, never settled firsthand over the bestiary, is: **which of
these three ingredients passes kernel `decide`, and which is walled?**

### Firsthand verdict (probe c.937, WSL env v4.31.0-rc1)

| Ingredient | Decidable? | Verdict |
|------------|-----------|---------|
| (H) `centralCorrect c j` — the central grid equality | **No** | **INTRINSIC** (whnf-wall) |
| (A) `evolve (2^j) (c.toGrid (0,0))` — reference evolution | **Yes** | `decide` |
| (B) bounds `[2^j, 2^j + 2^(j+1))` — pure `Int` arithmetic | **Yes** | `decide` |

The hypothesis (H) is **in the same INTRINSIC wall class** as the six `hashlife_*`
theorems of `Computation.lean` (probed in `DecideProbe.lean`): proving
`centralCorrect c 0` requires reducing `hashlifeResultAux 2 c`, whose recursion over
the `MacroCell` quadtree does not terminate at the kernel. The probe confirms:
`failed to synthesize Decidable (centralCorrect cexBlock1 0)`.

**Consequence for the G2/G3 attack (#6724)**: one CANNOT establish
`centralCorrect c j` over a bestiary witness by `decide`. The only path is to
**supply `h` as a hypothesis** (threaded from a P4.3 induction step) and then
consume `centralCorrect_mem` — exactly the strategy of `centralCorrect_mem_shift`
(L2443) and the P4.4 assembly. Ingredients (A) and (B), by contrast, are decidable
and instantiable over the bestiary (sanity checks below). This module **exercises
those two decidable sides**, confirming that the gate, once the hypothesis is
supplied, discharges entirely by computation.

### Constraints

Pure kernel-`decide`, **zero native axiom**, `native_decide` forbidden, bounded
compile budget (`j ≤ 1`). EPIC #3846 / #6724 / #9568. Sorry-free.
-/

/-
  i18n convention (EPIC #4980, user decision 2026-07-04): this file is the
  **English mirror** of the FR-canonical `AdversarialBatteryG2.lean`. Theorem
  statements, Lean tactics, lemma names and Mathlib references stay in English
(compat Mathlib 4); only the docstrings and this header block differ between the
  two files.
-/

import Conway.Life.AdversarialBattery_en
import Conway.Life.HashlifeCorrectness

namespace Conway_en
open Conway
namespace Life_en
open Life

/-! ## Ingredient (H) — the `centralCorrect` hypothesis is INTRINSIC

The probe confirms firsthand that `centralCorrect c 0` is not kernel-decidable
over the bestiary witnesses: the `Decidable` instance fails to synthesize, because
the central grid equality crosses `hashlifeResultAux (j+2) c` whose MacroCell
recursion does not reduce. `by decide` code held as a comment + verdict, in the
style of `DecideProbe.lean` (to reproduce the error verbatim, uncomment).

  `centralCorrect cexEmpty1 0`: NOT kernel-decidable — `hashlifeResultAux` does
  not reduce at the kernel (whnf-wall, INTRINSIC class). Probe verdict c.937:
  `failed to synthesize Decidable`. Same class for `cexBlock1 0`.
-/

-- theorem cexEmpty1_centralCorrect_j0 : centralCorrect cexEmpty1 0 := by decide
-- theorem cexBlock1_centralCorrect_j0 : centralCorrect cexBlock1 0 := by decide

/-! ## Ingredient (A) — the `evolve` "alive" side IS decidable

The reference-evolution side of `centralCorrect_mem` reduces entirely at the
kernel: `evolve (2^j)` over the grid of a level-1 MacroCell witness is a finite
computation over a small grid. The 2×2 block being a still life, `evolve 1` fixes
it; the empty cell stays empty. These are the real (honest) sanity checks of the
gate.
-/

/-- **Sanity (A)**: the 2×2 block is a still life — `evolve 1` leaves it invariant.
    This is the "alive" side of the G2 gate for `cexBlock1` at `j = 0`. -/
theorem cexBlock1_evolve1_fixed :
    evolve 1 (cexBlock1.toGrid (0, 0)) = cexBlock1.toGrid (0, 0) := by decide

/-- **Sanity (A)**: the empty cell is fixed under `evolve 1` (vacuity preserved). -/
theorem cexEmpty1_evolve1_fixed :
    evolve 1 (cexEmpty1.toGrid (0, 0)) = cexEmpty1.toGrid (0, 0) := by decide

/-- **Sanity (A)**: cell (0, 0) stays alive after one evolution step of the block
    (the block is a still life; each cell has 3 neighbors and survives under
    B3/S23). Instantiation of the "alive" conjunct of `centralCorrect_mem`. -/
theorem cexBlock1_cell_alive_evolve1 :
    isAlive (evolve 1 (cexBlock1.toGrid (0, 0))) (0, 0) = true := by decide

/-- **Sanity (A)**: in the empty witness, (0, 0) is dead after one step. -/
theorem cexEmpty1_cell_dead_evolve1 :
    isAlive (evolve 1 (cexEmpty1.toGrid (0, 0))) (0, 0) = false := by decide

/-! ## Ingredient (B) — the central-window bounds ARE decidable

The "bounds" conjunct of `centralCorrect_mem` is pure `Int` arithmetic: the
central window of level `j` is `[2^j, 2^j + 2^(j+1))` on each axis
(`j = 0` → `[1, 3)`, `j = 1` → `[2, 6)`). Fully kernel-`decide`. The theorems
below classify bestiary coordinates as inside / outside the window, confirming
that the gate geometry discharges by computation as soon as hypothesis (H) is
supplied.
-/

/-- **Sanity (B, j = 0)**: the central window `[1, 3)` contains the inner corner
    `1` (lower bound attained). -/
theorem central_window_j0_contains_lower_bound :
    (2^0 : Int) ≤ (1 : Int) ∧ (1 : Int) < (2^0 : Int) + 2^1 := by decide

/-- **Sanity (B, j = 0)**: the central window `[1, 3)` EXCLUDES the absolute corner
    `0` (lower bound not attained — this is the counter-example that killed the NW
    wall `p4_nw_overlap_wall` in c.91: a block at the absolute NW corner is outside
    the window). -/
theorem central_window_j0_excludes_nw_abs_corner :
    ¬ ((2^0 : Int) ≤ (0 : Int) ∧ (0 : Int) < (2^0 : Int) + 2^1) := by decide

/-- **Sanity (B, j = 1)**: the central window `[2, 6)` contains the inner corner
    `2`. Instantiation at level `j = 1` (level-2 cell, 4×4 window). -/
theorem central_window_j1_contains_lower_bound :
    (2^1 : Int) ≤ (2 : Int) ∧ (2 : Int) < (2^1 : Int) + 2^2 := by decide

/-! ## Synthesis — the G2 gate discharges except for the hypothesis

Under hypothesis `h : centralCorrect cexBlock1 0`, the membership of a point in
the hashlife result reduces — via `centralCorrect_mem` — to an "alive" conjunct
(A) AND a "bounds" conjunct (B), both of whose sides are kernel-decidable (above).
The INTRINSIC wall is pushed onto (H): `centralCorrect` itself, which requires the
`hashlifeResultAux` recursion. Proof strategy confirmed for the P4.4 assembly
(#6724): thread `h` from P4.3, then consume the gate.
-/

end Life_en
end Conway_en
