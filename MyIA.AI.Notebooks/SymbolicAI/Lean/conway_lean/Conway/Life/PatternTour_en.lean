/-
! # A tour of Game of Life patterns

This module is a **pedagogical path** through the bestiary of Conway's Game of Life
patterns. It defines no new theory: it *runs* the existing theory and *proves* it on
concrete examples, following a single narrative thread — the progression of dynamical
regimes:

  **equilibrium** (still lifes) → **cycle** (oscillators) → **translation** (spaceships)
                              → **serialization** (RLE) → **acceleration** (Hashlife).

Each section performs the same gesture twice: a `#eval` that *computes* the evolution
("watch the pattern live"), then a `theorem ... := by decide` that *proves* that what
we see is indeed the advertised property. The `decide` proofs run in the kernel without
adding axioms (cf. `Computation.lean` §6, the `ceilLog2` fix #9536); the rare
`native_decide` calls (pulsar, gun) are flagged and add the `Lean.ofReduceBool` axiom —
the formal equivalent of a witness `#eval`.

The i18n convention is Pattern A (cf. `code-style.md`, EPIC #4980): this file is the
English mirror; the French canonical lives in `PatternTour.lean`. Only docstrings and
comments differ; statements, tactics and proofs are byte-identical across the two files.
-/

import Conway.Life
import Conway.Life.Oscillators
import Conway.Life.Spaceships
import Conway.Life.RLE
import Conway.Life.Computation

namespace Conway_en
open Conway
namespace Life_en
open Life
open Conway.Life.RLE

/-! ## §1. Equilibrium — still lifes

A *still life* is a stable configuration: applying one step of the Game of Life leaves
it unchanged. This is not inertia — every live cell must have exactly two or three
neighbours, and every dead cell must have anything but three, so that nothing moves.
The smallest non-trivial still life is the *block* (2×2); the classics `loaf`, `boat`,
`tub`, `pond`, `ship` show the variety of possible local equilibria.

We *watch* the equilibrium (the `#eval` returns `true`), then *prove* it in the kernel
(`decide`, zero axioms). -/

-- The loaf is a 7-cell still life. The computation confirms stability.
#eval isStillLife loaf      -- expected: true
#eval (step loaf) == loaf   -- expected: true (explicit single-step reduction)

/-- The loaf is a still life: one step leaves it invariant. Proof by `decide` in the
    kernel, zero axioms added. -/
theorem loaf_is_still_life : isStillLife loaf = true := by decide

/-- The tub is a 4-cell still life. Kernel proof, zero axioms. -/
theorem tub_is_still_life : isStillLife tub = true := by decide

/-! ## §2. Cycle — oscillators

An *oscillator of period n* returns to itself after exactly n steps, without moving.
The `blinker` (3 cells in a line, period 2) is the most famous; the `beacon` (period 2)
and the `toad` (period 2) are other compact oscillators. For larger structures, the
`pulsar` (48 cells, period 3) and the `pentadecathlon` (period 15) exceed the kernel's
recursion limit: we switch to `native_decide`, which compiles the computation and adds
the `Lean.ofReduceBool` axiom.

The `decide` → `native_decide` switch is exactly the diagnostic documented in cycle c.736
in `decidable_instance_propagation.md`: on Game of Life state predicates, `decide` holds
up to a moderate recursion depth, then yields to native evaluation. -/

-- The beacon oscillates with period 2.
#eval isOscillator beacon 2       -- expected: true
#eval (evolve 1 beacon) == beacon -- expected: false (half-period changes the shape)

/-- The beacon is a period-2 oscillator. Kernel proof, zero axioms. -/
theorem beacon_is_oscillator : isOscillator beacon 2 = true := by decide

-- The pulsar (48 cells) exceeds the kernel recursion limit: native evaluation.
#eval isOscillator pulsar 3       -- expected: true
#eval (evolve 3 pulsar) == pulsar -- expected: true (one full period)

/-- The pulsar is a period-3 oscillator. The predicate ranges over 48 cells; `decide`
    fails here by recursion limit (`maxRecDepth`), so we resort to `native_decide`: the
    computation is compiled, and the proof rests on the `Lean.ofReduceBool` axiom. This
    is the formal equivalent of a witness `#eval`. -/
theorem pulsar_is_oscillator : isOscillator pulsar 3 = true := by native_decide

/-! ## §3. Translation — spaceships

A *spaceship* of period n and displacement v is the mobile version of an oscillator:
after n steps, the pattern reappears *translated* by v. The `glider` (5 cells) is the
smallest spaceship and the only diagonal one at c/4 (one cell diagonally every 4 steps).
The orthogonal spaceships `lwss`/`mwss`/`hwss` travel at c/2 (two cells horizontally
every 4 steps).

This is where the narrative thread tightens: **a spaceship is an oscillator in the
reference frame that translates with it.** The `#eval` computes the actual translation;
the theorem proves it. -/

-- The glider moves one cell diagonally (1, -1) every 4 steps.
#eval isSpaceship glider 4 (1, -1)        -- expected: true
#eval (evolve 4 glider) == shift (1,-1) glider  -- expected: true (computed translation)
#eval (evolve 8 glider) == shift (2,-2) glider  -- expected: true (two periods → 2× the displacement)

/-- The glider is a diagonal spaceship of period 4 and displacement (1, -1).
    Kernel proof, zero axioms. -/
theorem glider_is_spaceship : isSpaceship glider 4 (1, -1) = true := by decide

/-- The lightweight spaceship (`lwss`) is an orthogonal spaceship of period 4 and
    displacement (0, 2) — speed c/2. Kernel proof, zero axioms. -/
theorem lwss_is_spaceship : isSpaceship lwss 4 (0, 2) = true := by decide

/-- Uniformity of the glider's motion: after one more half-period (8 steps, i.e. two
    periods), the translation is exactly twice as far. This is the scale-invariance of
    the motion — the glider does not drift, it translates linearly. Kernel proof, zero
    axioms. -/
theorem glider_two_periods_translation : evolve 8 glider = shift (2, -2) glider := by decide

/-! ## §4. Serialization — the RLE format

The *Run-Length Encoded* (RLE) format is the lingua franca of Game of Life patterns: a
compact text file (`bo$2b3o!`) encodes a grid, readable by every simulator. The
`parseRLE` function (returning an `Except String Grid`) parses a string into a `Grid`;
`parseRLE!` is the wrapper that returns `[]` on error, convenient for `#eval`.

The pedagogical point: **the same pattern exists in two forms** — a hand-written
constant (`glider : Grid`) and a parsed string (`glider_parsed`) — and we can prove they
coincide. The *Gosper Glider Gun* (36 cells, 1970) is the first known finite pattern
with unbounded growth: it emits a glider every 30 steps, indefinitely. It is the link
between spaceships (§3) and computation (§5). -/

-- The Gosper gun parsed from its RLE string: 36 live cells.
#eval gosper_gun.length                       -- expected: 36
#eval (parseRLE gosper_gun_RLE).toOption.isSome  -- expected: true (well-formed RLE)

/- Pedagogical note: one might be tempted to state `theorem gosper_gun_has_36_cells
   : gosper_gun.length = 36 := by decide`. But `decide` fails here, stuck on the opacity
   of the parser: `gosper_gun := parseRLE! gosper_gun_RLE` is a non-`@[reducible]` `def`
   that the kernel does not unfold during `Decidable` instance synthesis (cf.
   `docs/lean/decidable_instance_propagation.md`, cycle c.939). The witness `#eval` above,
   which reduces by evaluation, is therefore the honest computational proof of this cell
   count — without adding the `Lean.ofReduceBool` axiom that `native_decide` would require.
   This is precisely the choice made by `Conway.Life.RLE` for its own checks. -/

-- Cross-checks serialization ↔ hand-written constant. The RLE lwss coincides exactly
-- with the constant; the RLE glider is the same pattern modulo a coordinate convention
-- (cf. `Conway.Life.RLE`), so we verify its cell count instead.
#eval glider_parsed.length        -- expected: 5 (same cardinality as `glider`)
#eval lwss_parsed == lwss         -- expected: true (exact coincidence)

/-! ## §5. Acceleration — Hashlife

`evolveHashlifeFast` advances a grid by `2^k` generations in a single step of the
recursive Hashlife algorithm, which exploits the redundancy of the plane's quadtree
structure. For periodic patterns (oscillators, spaceships, guns), Hashlife achieves
exponential speedup: advancing by 2^k generations costs essentially the same as
advancing by 2^(k-1).

The correctness of this "fast path" is proved against the naive reference `evolve`.
After the `ceilLog2` fix (#9536, resolving #8869), these equalities pass `decide` in the
kernel without adding axioms — the `MacroCell` layer is no longer opaque to the reducer.
This is the endpoint of the tour: the same evolution, computed by two algorithms of
radically different complexity, proved equal. -/

-- Hashlife vs reference: same result on the glider, at 4 and 8 generations.
#eval evolveHashlifeFast 4 glider == evolve 4 glider   -- expected: true
#eval evolveHashlifeFast 8 glider == evolve 8 glider   -- expected: true

-- The fast path recovers exactly the translation proved in §3.
#eval evolveHashlifeFast 4 glider == shift (1, -1) glider  -- expected: true
#eval evolveHashlifeFast 8 glider == shift (2, -2) glider  -- expected: true

/- The twin statement `evolveHashlifeFast 4 glider = evolve 4 glider` (coincidence with
   the reference) already lives in `Conway.Life.Computation.hashlife_fast_glider_4`. The
   tour derives the translation result here, linking §3 and §5: the fast path recovers
   exactly the displacement proved on the naive reference. -/

/-- The Hashlife fast path recovers, in a single `MacroCell` step, the diagonal
    translation (1, -1) that the reference computes step by step over 4 generations. This
    is the scale-invariance of §3 as seen from the accelerated algorithm. Kernel proof,
    zero axioms. -/
theorem hashlife_fast_glider_translation_4 : evolveHashlifeFast 4 glider = shift (1, -1) glider := by decide

/-! ## Coda

From the motionless `loaf` to the Gosper gun spitting out spaceships, Game of Life
patterns exhibit five dynamical regimes that one can, for each, both *watch run* (`#eval`)
and *prove* (`theorem ... := by decide`). The thread of this tour — equilibrium, cycle,
translation, serialization, acceleration — is itself the deliverable: it connects modules
that were hitherto independent (`Oscillators`, `Spaceships`, `RLE`, `Computation`) into a
single narrative, where each `theorem` is an anchor point and each `#eval` a living
witness. -/

end Life_en
end Conway_en
