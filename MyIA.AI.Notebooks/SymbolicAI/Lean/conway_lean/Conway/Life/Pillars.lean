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
| Unit cell           | Nicolay Beluchenko | 2011 | unitcell.rle  | 4 096       | ~7    |
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
- **Phase 3c patterns** (this file) : the four pillar patterns are
  still *placeholder empty grids* (RLE files too large for Lean
  string literals — they await a file-IO or pre-processing loading
  step). The witness theorems below are therefore **vacuously true**
  (empty grid is a fixed point, `evolveHashlifeFastMemo_empty`); they
  pin down the intended statements and will gain real content when
  the RLE-decoded grids replace the placeholders.
- **Future** : with real patterns loaded, each witness becomes a
  single `by native_decide` (gated by an appropriate budget raise),
  now made tractable by the memoization layer.

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
namespace Pillars

/-! ## Pattern archive

RLE files for the four pillars live in `patterns/` alongside this
Lean project. They were downloaded from the copy.sh mirror of the
LifeWiki community archive:

  `https://copy.sh/life/examples/<name>.rle`

| File                | Grid size    | Size (KB) | Pillar theorem            |
|---------------------|-------------|-----------|---------------------------|
| `otcametapixel.rle` | 2058 × 2058 | 165       | `otca_metapixel_witness`  |
| `p5760unitlifecell.rle` | 499 × 499 | 15     | `unitcell_witness`        |
| `turingmachine.rle` | variable    | 104       | (narrative: Act II)       |
| `gemini.rle`        | huge        | 5 300     | `gemini_witness`          |

`gemini.rle` (5.3 MB) is gitignored due to size; the notebook's
`fetch_rle()` re-downloads it on demand with disk caching.

The RLE files are **too large** for Lean string literals (OTCA alone is
165 KB of RLE text; the Lean kernel would need to parse it at compile
time). They await a future file-IO loading mechanism or external
pre-processing step that generates Lean `Grid` definitions from the
RLE source.

## Pattern placeholders

Each pillar needs (a) its initial RLE-decoded `Grid`, (b) the target
generation count, (c) the expected post-evolution `Grid` (also from
the published source). For the scaffold we declare opaque names with
trivial bodies ; the real patterns will be loaded via
`Conway.Life.RLE.parseRLE` in Phase 3c.

These are **defs**, not `axiom`s — they have a concrete trivial body
(`Grid.empty`) so no axiom is introduced. They will be replaced by
parsed RLE in the actual pillar PR. -/

/-- OTCA metapixel initial state. Loaded from RLE in Phase 3c. -/
def otcaInitial : Grid := ([] : Grid)

/-- OTCA metapixel state after one on/off cycle (35 328 generations).
    Loaded from RLE in Phase 3c. -/
def otcaTarget : Grid := ([] : Grid)

/-- Generation count for the OTCA metapixel on/off cycle. -/
def otcaGens : Nat := 35328

/-- UnitCell initial state. Loaded from RLE in Phase 3c. -/
def unitcellInitial : Grid := ([] : Grid)

/-- UnitCell state after one full period. Loaded from RLE in Phase 3c. -/
def unitcellTarget : Grid := ([] : Grid)

/-- Generation count for the UnitCell period (4 096). -/
def unitcellGens : Nat := 4096

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
The four pillar patterns (OTCA, UnitCell, Gemini, CPU) are too large
for Lean string literals (OTCA alone is 70 KB of RLE) and await a
future file-based loading mechanism. -/

/-- The Pulsar parsed from its RLE representation.
    Proven equal to the hand-written constant in RLE.lean. -/
def pulsarGrid : Grid := RLE.pulsar_parsed

/-- The Pulsar is a period-3 oscillator: after 3 generations it
    returns to its initial state. Proven via `native_decide`. -/
theorem pulsar_period3 :
    evolveHashlifeFast 3 pulsarGrid = pulsarGrid := by
  native_decide

/-! ## Witness theorems

Each theorem asserts that `evolveHashlifeFastMemo N pattern = target`
for the corresponding pillar. The proof is intended to be a single
`by native_decide` once memoization lands. -/

/-- **OTCA metapixel witness** — Brice Due 2006.

    The OTCA metapixel is a 2048×2048 period-35328 unit cell that can
    emulate any Life-like cellular automaton. When zoomed out, ON and
    OFF cells are clearly visible. It was the first programmable
    metacell, demonstrating that Life can simulate *itself*.

    Public demo: one full ON→OFF→ON cycle completes in 35 328 gens.
    RLE source: conwaylife.com/wiki/OTCA_metapixel (70 KB).

    Phase 3c : `by native_decide` with memoized Hashlife.
    Currently vacuous (placeholder empty grids, see Status above). -/
theorem otca_metapixel_witness :
    evolveHashlifeFastMemo otcaGens otcaInitial = otcaTarget :=
  evolveHashlifeFastMemo_empty otcaGens

/-- **UnitCell witness** — Nicolay Beluchenko 2011.

    A smaller OTCA-style metacell with period 4 096, roughly 9× the
    speed of OTCA. At level-7 quadtree this is the most tractable
    pillar — likely the first to land green once memoization is in
    place. The pattern uses a different internal architecture (p5760
    core) making it complementary to OTCA.

    Phase 3c : `by native_decide` with memoized Hashlife.
    Currently vacuous (placeholder empty grids, see Status above). -/
theorem unitcell_witness :
    evolveHashlifeFastMemo unitcellGens unitcellInitial = unitcellTarget :=
  evolveHashlifeFastMemo_empty unitcellGens

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

end Pillars
end Life
end Conway
