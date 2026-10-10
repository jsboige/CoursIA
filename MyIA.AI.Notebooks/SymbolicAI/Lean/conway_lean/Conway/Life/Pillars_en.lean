/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Pillars — Community-witness theorems (Phase 3c scaffolding)

This module is **scaffolding** for the four "pillars" of the Conway
Life community that we want to certify via `native_decide` once
memoized Hashlife (`Conway.Life.HashlifeMemo`) is in place.

### The four pillars

| Pillar              | Author       | Year | Pattern               | Generations | Level |
|---------------------|--------------|------|-----------------------|-------------|-------|
| OTCA metapixel      | Brice Due    | 2006 | OTCA-on/off transition| 35 328      | ~9    |
| Unit cell           | Nicolay Beluchenko | 2011 | p5760unitlifecell.rle | 5 760 | ~7  |
| Gemini              | Andrew Wade  | 2010 | gemini.rle           | 33 699 586  | ~14   |
| CPU (digital)       | Nicolay Beluchenko / Andy Stearns | 2016 | digital_cpu.rle | 1 048 576 | ~12   |

Each witness asserts that `evolveHashlifeFastMemo N pattern` produces
the expected target configuration after `N` generations. The
generation count is chosen at a notable milestone of the pattern's
public demo (e.g. the OTCA "one on/off cycle" is 35 328 generations,
the published Gemini self-replication completes in 33 699 586).

### Status

- **Phase 3b** : `hashlifeResultAux` proven structurally recursive,
  light-cone bound `mem_lightCone_of_manhattan_le` closed (PR #2173).
  Remaining sorries in `Conway.Life.HashlifeCorrectness` are
  level-2/step containment lemmas, independent of this file.
- **Phase 3c memoization** : DONE. `Conway.Life.HashlifeMemo` now
  provides a real fuel-keyed memoized Hashlife
  (`evolveHashlifeFastMemo`) proven equal to the Phase 3b reference
  (`evolveHashlifeFastMemo_eq_evolveHashlifeFast`, no sorry).
- **Phase 3c patterns** (this file) : the UnitCell (15 KB) then the OTCA
  (165 KB) are now genuinely loaded (`include_str` + `RLE.parseRLE!`,
  see below) — the file-loading mechanism this module awaited has existed
  since Lean 4.33, and the kernel parses the archive's largest RLE without
  a source literal. Gemini and CPU remain *placeholder empty grids* (Gemini's
  RLE is gitignored, the CPU's is absent) and their witnesses remain
  **vacuously true** (`evolveHashlifeFastMemo_empty`).
- **The RLE on disk is not the pillar's pattern** : this row targeted
  Beluchenko's UnitCell (2011, period **4 096**), but the archive only holds
  `p5760unitlifecell.rle` — the "closest available", which
  `patterns/README.md` credits to **David Bell** with period **5 760**.
  Measurement of 2026-10-09: the latter really is period 5 760, so "4 096" was
  not a wrong number — it describes **a different pattern**, absent from the
  archive. The `unitcellGens := 5760` below therefore describes the pattern
  **actually loaded**. The authorship (Beluchenko 2011 here, David Bell in
  `patterns/README.md`) remains **open** : measurement does not settle
  attribution.
- **The UnitCell period witness is NOT EXPRESSIBLE in this engine**
  (measured 2026-10-09, #19989) — and it is not a budget question:
  `Grid` is a sparse **borderless** list (`evolveHashlifeFastMemo` falls back
  to `evolve`), while the UnitCell is an **open system** that emits gliders
  which leave forever. Sparse simulator calibrated against `life_synthesize`:
  over 8 000 generations the population stays ~4 840 while the extent grows
  from 499² to 3 705 × 3 795, and **no state ever repeats** — so
  `evolveHashlifeFastMemo N unitcellInitial = unitcellInitial` has no solution
  `N`. The period **5 760** is nevertheless confirmed *borderlessly* on a
  **500 × 500 torus** (first repetition gen 11324 == gen 5564), which
  validates both the source filename and the "5 760" row of
  `patterns/README.md`.
  Formalizing it needs a **toroidal** engine, absent from the lake: that is
  the natural continuation of this tranche.
- **The OTCA, by contrast, is a CLOSED system — measured 2026-10-09
  (#19989, tranche 3)**: over 1 800 generations the extent stays
  **strictly** 2058 × 2058 (no cell ever outside the initial box at any
  sampled generation — a glider born between two samples would still be
  visible at the next one, since gliders do not die), while the
  population oscillates within [63 955, 64 798]: the machinery runs, but
  **nothing escapes** — unlike the UnitCell. The prediction "an isolated
  metapixel on a borderless grid is not periodic either" is therefore
  **refuted for the OTCA**. The period witness
  `evolveHashlifeFastMemo 35328 otcaInitial = otcaInitial` remains
  expressible in principle — but tranche 4 **measured** its cost: the
  `native_decide` evaluation does not terminate within 2 h on this
  machine (two attempts, no success line, no `.olean` produced). The
  35,328 period stays quoted, not certified by the organ: a measured
  ceiling, liftable on a better-endowed machine.
- **Paired negative witnesses** (criterion 2 of #19989):
  `pulsar_period1_negative` and `pulsar_period2_negative` accompany
  `pulsar_period3`, so the period is **exactly** 3 and not merely a divisor of
  3. This is the lake's only **positive** period witness, hence the only
  one that can receive a pair: for the UnitCell the pair is impossible
  *a fortiori* (the positive is not expressible — open system,
  measured, see above); for the OTCA the positive remains expressible
  in principle but its evaluation exceeds the measured ceiling
  (tranche 4, see above); for Gemini/CPU the grids are still empty,
  where a negative would measure nothing real.
- **Future** : the CPU (once its RLE is loaded by the same mechanism) — its
  border question remains to be settled by the same measurement method.

### Why a separate file ?

These theorems exercise `native_decide` on large patterns; compile
times explode (`9^k` recursion on each subcell). Keeping them in a
distinct module lets the rest of `Conway.Life` build quickly while
`Pillars.lean` can be opted into via `lake build Conway.Life.Pillars`
when needed.

### Why scaffold the witnesses now ?

User mandate 2026-06-01 : prepare a complete-presentation scaffold so
that the §11 roadmap of `Lean-16b-Conway-Game-of-Life-Lean.ipynb` is concrete and
visible. Memoization was validated at the start of Phase 3 ; the
witnesses are the natural endpoint.
-/

import Conway.Life
import Conway.Life.MacroCell
import Conway.Life.Hashlife
import Conway.Life.HashlifeMemo
import Conway.Life.RLE

namespace Conway
namespace Life
namespace Pillars_en

/-! ## Pattern archive

RLE files for the four pillars live in `patterns/` alongside this
Lean project. They were downloaded from the copy.sh mirror of the
LifeWiki community archive:

  `https://copy.sh/life/examples/<name>.rle`

| File                | Grid size    | Size (KB) | Pillar theorem            |
|---------------------|-------------|-----------|---------------------------|
| `otcametapixel.rle` | 2058 × 2058 | 165       | `otca_initial_population` |
| `p5760unitlifecell.rle` | 499 × 499 | 15     | `unitcell_initial_population` |
| `turingmachine.rle` | variable    | 104       | (narrative: Act II)       |
| `gemini.rle`        | huge        | 5 300     | `gemini_witness`          |

`gemini.rle` (5.3 MB) is gitignored due to size; the notebook's
`fetch_rle()` re-downloads it on demand with disk caching.

The RLE files are **too large** for Lean string literals (OTCA alone is
165 KB of RLE text; the Lean kernel would need to parse it at compile
time). A file-loading mechanism does exist since Lean 4.33, however:
`include_str` embeds the content at compile time, with the path relative
to the source file. It is used below for the UnitCell (15 KB) and the OTCA
(165 KB) ; only Gemini (gitignored) remains to be done.

## Pattern placeholders

Each pillar needs (a) its initial RLE-decoded `Grid`, (b) the target
generation count, (c) the expected post-evolution `Grid` (also from
the published source). For the scaffold we declare opaque names with
trivial bodies ; the real patterns will be loaded via
`Conway.Life.RLE.parseRLE` in Phase 3c.

These are **defs**, not `axiom`s — they have a concrete trivial body
(`Grid.empty`) so no axiom is introduced. They will be replaced by
parsed RLE in the actual pillar PR. -/

/-- OTCA metapixel RLE source, embedded at compile time via `include_str`.
    The path is relative to THIS file (`Conway/Life/`). At 165 KB it is the
    largest pattern ever loaded into the lake — the "too large for the
    kernel" assumption is exactly what this tranche tests (see Status
    above). -/
def otcaRLE : String := include_str "../../patterns/otcametapixel.rle"

/-- OTCA metapixel initial state, decoded from the RLE by the repository's
    **proven** parser (`Conway.Life.RLE.parseRLE`). Measured population:
    64 691 live cells in a 2058 × 2058 box. -/
def otcaInitial : Grid := RLE.parseRLE! otcaRLE

/-- Generation count of the metacell's on/off cycle (published value from
    Brice Due's demo). -/
def otcaGens : Nat := 35328

/-- UnitCell RLE source, embedded at compile time via `include_str`.
    The path is relative to THIS file (`Conway/Life/`), not to the package
    root. -/
def unitcellRLE : String := include_str "../../patterns/p5760unitlifecell.rle"

/-- UnitCell initial state, decoded from the RLE by the repository's
    **proved** parser (`Conway.Life.RLE.parseRLE`). Measured population:
    4 761 live cells on a 499 × 499 box. -/
def unitcellInitial : Grid := RLE.parseRLE! unitcellRLE

/-- Generation count for one period of the pattern **actually loaded**:
    **5 760**, a measured value (see "Status" above). The `4 096` that stood
    here describes Beluchenko's UnitCell, which is **not** the archive's
    pattern (`p5760unitlifecell.rle`, cf. `patterns/README.md`). -/
def unitcellGens : Nat := 5760

/-- Gemini self-replicator initial state. Loaded from RLE in Phase 3c. -/
def geminiInitial : Grid := ([] : Grid)

/-- Gemini state after one full self-replication cycle (33 699 586 gens). -/
def geminiTarget : Grid := ([] : Grid)

/-- Generation count for one Gemini self-replication cycle. -/
def geminiGens : Nat := 33699586

/-- Digital CPU initial state. Loaded from RLE in Phase 3c. -/
def cpuInitial : Grid := ([] : Grid)

/-- Digital CPU state after a representative cycle (1 048 576 gens). -/
def cpuTarget : Grid := ([] : Grid)

/-- Generation count for one Digital CPU cycle. -/
def cpuGens : Nat := 1048576

/-! ## RLE-proven witness example

The Pulsar (period-3 oscillator) is parsed from RLE in our RLE.lean
module and verified as an oscillator. It serves as a concrete
demonstration that the RLE → Grid → evolve pipeline works end-to-end.
The UnitCell (15 KB) then the OTCA (165 KB) are now loaded via
`include_str` (see above); Gemini (gitignored) and CPU (RLE absent)
await the same wiring. -/

/-- The Pulsar parsed from its RLE representation.
    Proven equal to the hand-written constant in RLE.lean. -/
def pulsarGrid : Grid := RLE.pulsar_parsed

/-- The Pulsar is a period-3 oscillator: after 3 generations it
    returns to its initial state. Proven via `native_decide`. -/
theorem pulsar_period3 :
    evolveHashlifeFast 3 pulsarGrid = pulsarGrid := by
  native_decide

/-- **Paired negative witness** for `pulsar_period3`: the period is not 1 —
    the Pulsar is not a still life. Without this check, `pulsar_period3`
    alone would say nothing about the value `3`, only about *some* divisor
    of 3. -/
theorem pulsar_period1_negative :
    evolveHashlifeFast 1 pulsarGrid ≠ pulsarGrid := by
  native_decide

/-- **Paired negative witness**: the period is not 2 either. Together the two
    negatives establish that the period is **exactly** 3. -/
theorem pulsar_period2_negative :
    evolveHashlifeFast 2 pulsarGrid ≠ pulsarGrid := by
  native_decide

/-! ## Witness theorems

Each theorem asserts that `evolveHashlifeFastMemo N pattern = target`
for the corresponding pillar. The proof is intended to be a single
`by native_decide` once memoization lands. -/

/-- **OTCA metapixel** — Brice Due 2006.

    The first programmable metacell: 2058 × 2058, 64 691 live cells,
    able to emulate any Life-like cellular automaton — Life simulating
    *itself*. When zoomed out, the metacell's ON and OFF states are
    visible. The published ON→OFF→ON cycle completes in 35 328
    generations (source: conwaylife.com/wiki/OTCA_metapixel).

    **There is still no period witness here — but the postponement is
    now measured, not merely motivated.** Motivating measurement
    (dense simulator, 1 800 generations): the extent stays strictly
    2058 × 2058, no cell ever leaves the box, the population
    oscillates within [63 955, 64 798] — a **closed** system. The
    witness `evolveHashlifeFastMemo 35328 otcaInitial = otcaInitial`
    was attempted in tranche 4: its `native_decide` evaluation does
    not terminate within 2 h on this machine — the lake replays are
    consumed within seconds, then silence until the deadline, with no
    success line and no `.olean`. A measured ceiling of the organ on
    this witness, liftable on a better-endowed machine.

    What is proven here, and **non-vacuously**, is that the loaded grid
    is real: 165 KB of RLE through the same `include_str` +
    `RLE.parseRLE!` pipeline as the UnitCell — the
    `evolveHashlifeFastMemo_empty` route is closed for this pattern. -/
theorem otca_initial_population : otcaInitial.length = 64691 := by
  native_decide

/-- The loaded OTCA grid is not empty. Independent cross-check: the same
    population (64 691) is measured by direct Python counting of the `o`
    runs in the source RLE. -/
theorem otca_initial_nonempty : otcaInitial ≠ ([] : Grid) := by
  native_decide

/-- **UnitCell** — Nicolay Beluchenko 2011.

    A smaller OTCA-style metacell with period **5 760**, roughly 9× the speed
    of OTCA. The pattern uses a different internal architecture (p5760 core)
    making it complementary to OTCA.

    **There is no period witness here, and that is a result, not an
    omission.** The 5 760 period is not expressible in this engine: `Grid` is
    a sparse **borderless** list (`evolveHashlifeFastMemo` falls back to
    `evolve`), and the UnitCell is an **open system** — it emits gliders that
    leave forever. Measurement (sparse simulator calibrated against
    `life_synthesize`): over 8 000 generations the population stays ~4 840
    while the extent grows from 499² to 3 705 × 3 795, and **no state ever
    repeats** — so `evolveHashlifeFastMemo N unitcellInitial = unitcellInitial`
    has no solution `N`.

    The period is real, but belongs to the **tiled** reading: measured
    *borderlessly* on a 500 × 500 torus (first repetition gen 11324 ==
    gen 5564, i.e. 5 760). Formalizing it needs a toroidal engine, which does
    not exist in the lake — that is the continuation of this tranche.

    What IS provable here, and **non-vacuous**, is that the loaded grid is
    real: exactly what the `evolveHashlifeFastMemo_empty` route used by the
    other three witnesses closes off. -/
theorem unitcell_initial_population : unitcellInitial.length = 4761 := by
  native_decide

/-- The loaded UnitCell grid is non-empty — the
    `evolveHashlifeFastMemo_empty` route is therefore **closed** for this
    pattern, which makes the period witness impossible *a fortiori*.
    Independent cross-check: the same population (4 761) is measured by
    `scripts/lean/rle_to_lean_grid.py`. -/
theorem unitcell_initial_nonempty : unitcellInitial ≠ ([] : Grid) := by
  native_decide

/-- **Gemini witness** — Andrew Wade 2010.

    The first self-replicating universal constructor in Life. Gemini
    creates a complete copy of itself in 33 699 586 generations across
    a level-14 quadtree. This is the **flagship witness** — it
    demonstrates that Life is capable of open-ended self-replication,
    the strongest form of universality. Named for the Gemini
    constellation (twins).

    This is the hardest target: level-14 quadtree + 33M generations.
    Phase 3c : `by native_decide` with memoized Hashlife.
    Currently vacuous (placeholder empty grids, see Status above). -/
theorem gemini_witness :
    evolveHashlifeFastMemo geminiGens geminiInitial = geminiTarget :=
  evolveHashlifeFastMemo_empty geminiGens

/-- **Digital CPU witness** — Beluchenko / Andy Stearns 2016.

    A programmable digital CPU constructed from OTCA metapixels. It
    executes one instruction cycle in 1 048 576 generations (level-12
    quadtree). Demonstrates that Life can implement arbitrary
    computation — not just simulate a cell, but run a program.
    Detailed in Adam P. Goucher's 2016 analysis on the conwaylife.com
    forum.

    Phase 3c : `by native_decide` with memoized Hashlife.
    Currently vacuous (placeholder empty grids, see Status above). -/
theorem cpu_witness :
    evolveHashlifeFastMemo cpuGens cpuInitial = cpuTarget :=
  evolveHashlifeFastMemo_empty cpuGens

end Pillars_en
end Life
end Conway
