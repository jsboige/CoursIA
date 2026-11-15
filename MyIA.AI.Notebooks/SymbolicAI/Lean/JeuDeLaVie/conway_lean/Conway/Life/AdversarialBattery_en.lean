/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Adversarial battery (c.91 cribleur) — validation of candidate universal statements

Cribleur module (#9568-A): a **bestiary of pathological configurations** on which
any candidate universal statement — inherited OR new — must be instantiated
BEFORE any prover iteration. Generalizes the c.91 probe (#9565) that killed the
three NW-arm lemmas of P4 (`p4_nw_overlap_wall` / `p4_nw_g3_bridge` /
`p4_nw_supercell_agree`): the binder `p : Int × Int` was free there while the
supercell represents only the **central window** of the parent, and a trivial
counter-example (2×2 block at the absolute NW corner, `k = 1`) falsified the
statement from the start. The specialization test `exact` at the call site only
proved the statement's **sufficiency** (it closes the goal), never its
**satisfiability**.

### Two usage modes (on any candidate statement, before any prover cycle)

1. **Falsification**: instantiate the statement on each bestiary witness, `decide`
   the conclusion. Satisfied hypotheses + false conclusion ⇒ the statement is
   dead, a counter-example theorem in the `..._counterexample` style (#9565)
   certifies it. This mode killed the NW/SE/SW walls (c.91).
2. **Sanity**: the statement restricted to the bestiary must `decide` to `true`
   (a **necessary**, not sufficient condition — a green cribleur is never a proof,
   but a red one is fatal). The `cex*_sanity` theorems below guarantee the
   bestiary is **well formed**: each witness has the GoL property it is meant to
   exercise (still life, oscillator, spaceship, vacuity, death).

### Constraints

Every proof in this module is pure kernel-`decide` (reducibility acquired by the
`ceilLog2` rewrite #9536), **zero native axiom**, `native_decide` forbidden,
bounded compile budget (`k ≤ 2`). EPIC #3846 / #6724. Sorry-free.

### Grid layer vs MacroCell layer

The bestiary provides BOTH layers: (a) positioned **`Grid` witnesses**, to crible
universal locality statements like `evolve_box_agree` (#9577) and upcoming
bounded re-statements; (b) **`MacroCell` witnesses** (public generalization of
`p4CexBlock1`/`p4CexEmpty1` from #9565) to crible the P4 assembly statements at
the supercell scale.
-/

/-
  English mirror of `AdversarialBattery.lean` (FR canonical). Convention EPIC
  #4980 (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct
  FR + EN sibling files. The module docstring and public theorem docstrings below
  differ from the FR version; signatures, proofs and tactics remain
  byte-identical between the two files.
-/

import Conway.Life
import Conway.Life.MacroCell

namespace Conway_en
open Conway
namespace Life_en
open Life
open MacroCell

/-! ## Grid layer — positioned witnesses + sanity (decide)

Canonical configurations positioned to exercise edge pathologies: block (docile
still life) at the four corners, blinker straddling a boundary, glider directed
out-of-window, empty universe, full universe (overpopulation).
-/

/-- Witness: empty universe (vacuity — `evolve` preserves it). -/
def cexEmpty : Grid := []

/-- Witness: 2×2 block (still life) at the absolute NW corner of a window
    `[0, ...)²`. This is the configuration that killed the NW wall
    (`p4_nw_overlap_wall`, #9565): it persists (LHS `true`) while the RHS
    evaluated at `(-1,-1)` is out of window (`false`). -/
def cexBlockNW : Grid := block

/-- Witness: 2×2 block shifted to `(2, 2)` (inner corner — still inside the
    central window for `k = 2`, exercising the margin boundary). -/
def cexBlockShifted : Grid := shift (2, 2) block

/-- Witness: horizontal blinker (period-2 oscillator) at the origin — straddling
    the window boundary under a 1-step evolution (`step` stretches it vertical,
    spilling outside the original box). -/
def cexBlinker : Grid := blinker_h

/-- Witness: glider (5 cells) directed toward the SE corner — a spaceship that
    **exits** any bounded window in 4 steps, exercising "bleed off the edge". -/
def cexGlider : Grid := glider

/-- Witness: full 4×4 window (`k = 1`) — overpopulation: every cell has 8 live
    neighbors and dies in 1 step (B3/S23 requires 2-3 to survive). -/
def cexFull1 : Grid :=
  [(0, 0), (0, 1), (0, 2), (0, 3),
   (1, 0), (1, 1), (1, 2), (1, 3),
   (2, 0), (2, 1), (2, 2), (2, 3),
   (3, 0), (3, 1), (3, 2), (3, 3)]

/-- **Sanity**: the empty witness is a still life (vacuity preserved). -/
theorem cexEmpty_stillLife : isStillLife cexEmpty = true := by decide

/-- **Sanity**: the NW-corner block is a still life (the docile pattern that
    killed the NW wall — it persists, so LHS = `true`). -/
theorem cexBlockNW_stillLife : isStillLife cexBlockNW = true := by decide

/-- **Sanity**: the shifted block is still a still life (translation preserves
    still-life character — `shift` invariance). -/
theorem cexBlockShifted_stillLife : isStillLife cexBlockShifted = true := by decide

/-- **Sanity**: the blinker is a period-2 oscillator (exercises boundary spill at
    each half-period). -/
theorem cexBlinker_period2 : isOscillator cexBlinker 2 = true := by decide

/-- **Sanity**: the glider is a spaceship of period 4 and displacement `(1, -1)`
    (canonical vector `glider_spaceship` from `Life.lean`, exercises "bleed off
    the edge" — exits the bounded window). -/
theorem cexGlider_spaceship : isSpaceship cexGlider 4 (1, -1) = true := by decide

/-- **Sanity**: the full 4×4 window is NOT a still life (overpopulation — `step`
    kills it). `false` here is expected and confirms the witness. -/
theorem cexFull1_notStillLife : isStillLife cexFull1 = false := by decide

/-! ## MacroCell layer — supercell witnesses (public generalization of #9565)

The `p4CexBlock1`/`p4CexEmpty1` witnesses from #9565 are `private` in
`HashlifeCorrectness`; this section provides **public** versions and generalizes
the block to the four quadrants, to crible the bounded re-statements of the P4
walls/bridges at the supercell scale.
-/

/-- Empty level-1 cell (MacroCell witness of the #9565 counter-example). -/
def cexEmpty1 : MacroCell :=
  node (leaf false) (leaf false) (leaf false) (leaf false)

/-- Full level-1 cell — 2×2 block, a still life (MacroCell witness #9565). -/
def cexBlock1 : MacroCell :=
  node (leaf true) (leaf true) (leaf true) (leaf true)

/-- Level-2 cell (4×4 window) whose NW quadrant alone is a 2×2 block, the
    other 3 quadrants empty — the exact instantiation of the #9565
    counter-example (`nw = block`, rest empty), made public to re-crible the
    bounded re-statements of the P4 walls at the supercell scale. -/
def cexBlockNWcorner2 : MacroCell :=
  node cexBlock1 cexEmpty1 cexEmpty1 cexEmpty1

/-- **Sanity**: `cexBlockNWcorner2` is at level 2 (4×4 window = 16 cells,
    2 node levels above the leaves). -/
theorem cexBlockNWcorner2_level2 : cexBlockNWcorner2.level = 2 := by decide

/-! ## Crible of bounded NW re-statements (grain A.4, #9568-A / EPIC #6724)

The NW wall `p4_nw_overlap_wall` was killed (c.91, #9565) because the binder
`p : Int × Int` was **free** there: nothing constrained `p` to the central window
the supercell represents, and a 2×2 block at the absolute NW corner falsified the
statement from `p = r = (0,0)` (LHS `true`, RHS `false` — `(-1,-1)` structurally
outside the non-negative window of `toGrid`). The repair direction (refutation
block in `HashlifeCorrectness`) is to **bound `p` to the parent's central
window**, `2^k ≤ p.i < 2^(k+1)` on each axis, then transport via a Chebyshev
locality lemma.

This section cribs that bounded restriction on the NW witnesses of the bestiaire.
It confirms by `decide` (pure kernel, zero axiom, `native_decide` forbidden —
reducibility acquired via the `ceilLog2` rewrite #9536) three structural facts
that qualify the bounded candidate as a **survivor** (the restriction removes the
counter-example): (1) the live cells of `cexBlockNWcorner2` all lie OUTSIDE the
central window — the trace of counter-example #9565; (2) a typical central point
lies inside it (the window is non-vacuous); (3) the absolute NW corner `(0,0)`
(the `p` instantiation of the counter-example) is excluded — this is what makes
the unbounded statement false and the bounded one viable.

**Crible verdict**: bounded candidate = **survivor**. Freezing the canonical
statement (exact bound + Chebyshev transport + fixed universal statement) stays
with ai-01; this module only provides the `decide`-verified witnesses and
structural facts the freeze must satisfy. -/

/-- A cell `p` lies in the **central window** of level `k` (the centre of the
    level `k + 1` parent) iff each coordinate falls in `[2^k, 2^(k+1))`. This is
    the restriction that repairs the vacuity of the free `p` in the NW wall. -/
def inCentralWindow (k : Nat) (p : Int × Int) : Prop :=
  (2^k : Int) ≤ p.1 ∧ p.1 < (2^(k+1) : Int) ∧
  (2^k : Int) ≤ p.2 ∧ p.2 < (2^(k+1) : Int)

instance inCentralWindow.decidable (k : Nat) (p : Int × Int) :
    Decidable (inCentralWindow k p) := by
  unfold inCentralWindow; infer_instance

/-- **Crible A.4 — the NW block bleeds outside the central window.** The live
    cells of `cexBlockNWcorner2` (2×2 block in the NW quadrant of a 4×4 window)
    live at `{(0,0), (0,1), (1,0), (1,1)}`, all OUTSIDE the central window
    `[2, 4)²` (level `k = 1`). This is the structural trace of counter-example
    #9565: the block is "off-centre", exactly the pathology that killed the
    unbounded wall `p4_nw_overlap_wall`. Any bounded re-statement must therefore,
    for this witness, either restrict its conclusion to the central window (empty
    of live cells here) or exclude the witness by hypothesis. -/
theorem cexBlockNWcorner2_cells_outside_central :
    ∀ p ∈ cexBlockNWcorner2.toGrid (0, 0), ¬ inCentralWindow 1 p := by
  decide

/-- **Crible A.4 — the central window is non-vacuous.** The point `(2, 2)` (NW
    corner of the central window `[2, 4)²` at level `k = 1`) is indeed central.
    Confirms the bounded restriction is not empty: the central window contains
    real points, so the bounded statement has substantive scope, not a trivial
    elimination of all `p`. -/
theorem central_point_in_window : inCentralWindow 1 (2, 2) := by
  decide

/-- **Crible A.4 — the absolute NW corner is excluded by the bound.** The point
    `(0, 0)` (absolute NW corner, the `p = r` instantiation of counter-example
    #9565) is NOT central at level `k = 1`. This is what makes the unbounded
    statement false (the free `p` allows instantiating there) and the bounded
    statement a survivor (the restriction `2^k ≤ p.i` excludes it by
    construction). -/
theorem nw_corner_outside_central : ¬ inCentralWindow 1 (0, 0) := by
  decide

end Life_en
end Conway_en
