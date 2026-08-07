/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Phase 3b — Bounded correctness theorem for Hashlife

This module is **scaffolding for multi-agent prover iteration** (Epic #1453
harness co-evolution). Every theorem is stated precisely with `sorry`
placeholders. Each `sorry` is a self-contained prover target, ranked by
mathematical difficulty (P1 = easiest, P5 = hardest).

## Goal

The central theorem:

    theorem hashlife_correct (n : Nat) (g : Grid) (h : box_assez_grand g n) :
        evolveHashlifeFast n g = evolve n g

It says: given enough padding around `g`, the exponential-speedup Hashlife
implementation (`evolveHashlifeFast`) agrees with the reference step-by-step
implementation (`evolve`) after `n` generations.

## Proof strategy (5 lemmas)

The proof decomposes into 5 sub-goals. Each is a standalone `sorry` below.

  **P1. box_assez_grand_predicate** (trivial)
     Define the padding predicate. Pure definition, no proof.

  **P2. step_light_cone** (locality — the cone of dependence)
     After `t` generations, the state of cell `(r, c)` depends only on the
     initial state of cells within Manhattan distance `t`. This is B3/S23's
     "speed of light = 1 cell/generation".

  **P3. padCenter2_frame_lemma** (frame correctness)
     `padCenter2 c` correctly places `c` at the center of a level-`(k+2)`
     MacroCell, with `2^k` dead padding on each side.

  **P4. hashlifeResult_central_correct** (decompose-compose)
     On a level-`k` MacroCell `c` with adequate padding, `hashlifeResult c`
     equals `step^[2^(k-2)]` applied to the centered sub-region.

  **P5. hashlife_correct** (composition)
     Compose P2-P4 by induction on `n` to get the final theorem.

## Prover iteration protocol

Each `sorry` here is a target for `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/`.
The prover runs `lake build Conway.Life.HashlifeCorrectness` after each patch
and uses the `sorry_delta` as the forensic signal. As each `sorry` is
eliminated, the corresponding lemma is moved out of "scaffolding" status.

The difficulty rating drives agent selection:
  - P1/P2 (simple): local Qwen tactic agent
  - P3 (structural): z.ai GLM coordinator + tactic agent
  - P4 (compositional): OpenRouter frontier (Opus/GPT-5) Director escalation
  - P5 (induction): OpenRouter frontier with `--director-provider openrouter`

See `agent_tests/prover/RUNBOOK.md` for iteration protocol.

## Non-goals (out of scope for this module)

- Memoization / hash-consing (algorithmic performance, not correctness).
- Unbounded `hashlife_correct` without `box_assez_grand` hypothesis.
- Periodicity arguments for OTCA/Gemini (Phase 6-7).
-/

import Conway.Life
import Conway.Life.GridCanonical
import Conway.Life.MacroCell
import Conway.Life.Hashlife
-- EPIC #3846 cycle-break (ai-01 design-gate msg-...338lw8, 2026-07-11): the pure
-- Chebyshev geometry (`chebDist` family + `window_cheb_cone_in_domain`) now lives
-- in `Conway.Life.ConeGeometry` (Mathlib only). This import makes
-- `window_cheb_cone_in_domain` referenceable from the P5 `p5_large_n_jump` path
-- WITHOUT the circular reverse-import that would arise if it stayed in
-- `LightCone` (which imports this module). The proof-body wire (closing the
-- `p5_large_n_jump` sorry via the tight cone bound) is the next N2 step; this
-- import is the cycle-break enabler, cycle-free because `ConeGeometry` imports
-- Mathlib only.
import Conway.Life.ConeGeometry

namespace Conway
namespace Life

open MacroCell


/-! ## Module layout (Phase 3b split, PR A of #9863)

This aggregator used to be a 7082-line monolith. Per dispatch by
ai-01 on 2026-08-07T12:20:37Z (claim at issue #9863, lane
myia-po-2023:CoursIA), the body has been displaced into 9 sub-modules
under `Conway.Life.HashlifeCorrectness.*`:

  - `Conway.Life.HashlifeCorrectness.Padding` (L88-L536, 449 lines): P1 padding, marge n-aware, monotonie, borne de satisfiabilite
  - `Conway.Life.HashlifeCorrectness.Locality` (L537-L1083, 547 lines): P0 warm-up, P2 localite du cone, composition, P4.4, cone d'influence
  - `Conway.Life.HashlifeCorrectness.Bridges` (L1084-L1361, 278 lines): P3 correction, pont N2, well-formedness
  - `Conway.Life.HashlifeCorrectness.Decomposition` (L1362-L3591, 2230 lines): P4 central, pont forme canonique, cas de base, structural inputs, inductive, miroirs Chebyshev, bornes toCellsAux, agreement lemmas, quadrant characterization
  - `Conway.Life.HashlifeCorrectness.Walls.Common` (L3592-L3871, 280 lines): P4 (a) — the named overlap wall (abstract parent of all 4 quadrants)
  - `Conway.Life.HashlifeCorrectness.Walls.NW` (L3872-L4540, 669 lines): NW quadrant wall + refutation + supercell agree (c.91/c.92/c.93)
  - `Conway.Life.HashlifeCorrectness.Walls.NE` (L4541-L5073, 533 lines): NE quadrant wall (mirror of NW, c.8122)
  - `Conway.Life.HashlifeCorrectness.Walls.SW` (L5074-L5303, 230 lines): SW quadrant wall (L3324 NW-SE reflection, c.NNNN)
  - `Conway.Life.HashlifeCorrectness.Walls.SE` (L5304-L6492, 1189 lines): SE quadrant wall (diagonal mirror, c.90)

All proof bodies are byte-identical to the monolith (PR A = pure
displacement, no rewrite). The 38 allow-axioms names referenced by
the audit job in `.github/workflows/lean-conway.yml` depend only on
the `Conway.Life.*` namespace prefix, NOT on intermediate namespaces
or file paths — so the allow-list stays byte-identical across the split.
-/

import Conway.Life.HashlifeCorrectness.Padding
import Conway.Life.HashlifeCorrectness.Locality
import Conway.Life.HashlifeCorrectness.Bridges
import Conway.Life.HashlifeCorrectness.Decomposition
import Conway.Life.HashlifeCorrectness.Walls.Common
import Conway.Life.HashlifeCorrectness.Walls.NW
import Conway.Life.HashlifeCorrectness.Walls.NE
import Conway.Life.HashlifeCorrectness.Walls.SW
import Conway.Life.HashlifeCorrectness.Walls.SE

/-! ## P4 witnesses: base case k=0 (native_decide)

Concrete level-2 MacroCells verifying that the corrected P4 statement
holds on the base case `k = 0` (level-2 input, offset `(1,1)`, 1 generation).
Each `native_decide` confirms the theorem is satisfiable. -/

/-- Level-2 cell with the block pattern at positions (1,1)-(2,2). -/
private def blockCell : MacroCell :=
  MacroCell.node (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf true))
                 (MacroCell.node (leaf false) (leaf false) (leaf true)  (leaf false))
                 (MacroCell.node (leaf false) (leaf true)  (leaf false) (leaf false))
                 (MacroCell.node (leaf true)  (leaf false) (leaf false) (leaf false))

/-- Level-2 cell with a horizontal blinker at positions (0,1),(1,1),(2,1). -/
private def blinkerHCell : MacroCell :=
  MacroCell.node (MacroCell.node (leaf false) (leaf true) (leaf false) (leaf true))
                 (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf false))
                 (MacroCell.node (leaf false) (leaf true) (leaf false) (leaf false))
                 (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf false))

/-- Level-2 cell with the glider pattern at positions (0,1),(1,2),(2,0),(2,1),(2,2). -/
private def gliderCell : MacroCell :=
  MacroCell.node (MacroCell.node (leaf false) (leaf true)  (leaf false) (leaf false))
                 (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf true))
                 (MacroCell.node (leaf true)  (leaf true)  (leaf false) (leaf false))
                 (MacroCell.node (leaf true)  (leaf false) (leaf false) (leaf false))

/-- P4 base case k=0 on block (still life): centered 2x2 matches after 1 step. -/
theorem p4_base_block :
    (hashlifeResultAux 2 blockCell).toGrid (1, 1)
    = restrictGridTo (evolve 1 (blockCell.toGrid (0, 0))) 1 2 := by
  native_decide

/-- P4 base case k=0 on all-dead: trivially empty. -/
private def deadCell : MacroCell :=
  MacroCell.node (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf false))
                 (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf false))
                 (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf false))
                 (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf false))

theorem p4_base_dead :
    (hashlifeResultAux 2 deadCell).toGrid (1, 1)
    = restrictGridTo (evolve 1 (deadCell.toGrid (0, 0))) 1 2 := by
  native_decide

/-- P4 base case k=0 on glider: centered 2x2 matches after 1 step. -/
theorem p4_base_glider :
    (hashlifeResultAux 2 gliderCell).toGrid (1, 1)
    = restrictGridTo (evolve 1 (gliderCell.toGrid (0, 0))) 1 2 := by
  native_decide

/-- P4 base case k=0 on blinker: key test — cell (1,0) is outside center. -/
theorem p4_base_blinker :
    (hashlifeResultAux 2 blinkerHCell).toGrid (1, 1)
    = restrictGridTo (evolve 1 (blinkerHCell.toGrid (0, 0))) 1 2 := by
  native_decide

/-! ## P4 witnesses: recursive arms (k = 1, k = 2)

Concrete well-formed instances of the corrected statement exercising the
double-nine recursion (one layer at `k = 1`, two layers at `k = 2`). -/

/-- P4 witness at k = 1 (level-3, one recursion layer): a block (still
    life) centered in an 8×8 cell, 2 generations. -/
theorem p4_wf_witness_k1 :
    (centerInLevelPlus2 (node aliveLeaf aliveLeaf aliveLeaf aliveLeaf)).wf
        = true
    ∧ (hashlifeResultAux 3
          (centerInLevelPlus2
            (node aliveLeaf aliveLeaf aliveLeaf aliveLeaf))).toGrid
        ((2 : Int), (2 : Int))
      = restrictGridTo
          (evolve 2
            ((centerInLevelPlus2
              (node aliveLeaf aliveLeaf aliveLeaf aliveLeaf)).toGrid (0, 0)))
          2 4 := by
  native_decide

/-- P4 witness at k = 2 (level-4, two recursion layers): a glider
    centered in a 16×16 cell, 4 generations (the glider translates by
    `(+1, +1)`, staying inside the centered 8×8 window). -/
theorem p4_wf_witness_k2 :
    (centerInLevelPlus2 gliderCell).wf = true
    ∧ (hashlifeResultAux 4 (centerInLevelPlus2 gliderCell)).toGrid
        ((4 : Int), (4 : Int))
      = restrictGridTo
          (evolve 4 ((centerInLevelPlus2 gliderCell).toGrid (0, 0)))
          4 8 := by
  native_decide

/-! ## P5. Fuel-exhaustion invariant (Gap 1)

A definitional building block toward the full P5 theorem. The auxiliary
`evolveHashlifeFastAux` has a defensive branch `| 0, _, g => g` (fuel exhausted,
return the grid unchanged) which is only sound when `n = 0` has also been
reached. The lemma below discharges the relevant case directly: when `n = 0`,
the **first** pattern (`| _, 0, g => g`) fires regardless of the fuel value,
so the result is `g` independently of the fuel-exhaustion arm.

This is the first half of the Gap-1 invariant (the `n = 0` guard takes
priority over the fuel guard); the second half — proving the fuel-exhaustion
arm is unreachable on the real `evolveHashlifeFast n g = evolveHashlifeFastAux n n g`
call path when `n > 0` — remains open and is documented in `hashlife_correct`. -/

/-- When `n = 0`, `evolveHashlifeFastAux` returns `g` independently of the fuel
    value: the `n = 0` pattern (`| _, 0, g => g`) is matched before the
    fuel-exhaustion pattern (`| 0, _, g => g`). This discharges the fuel arm
    in the trivial case and is a prerequisite for reasoning about the
    fuel-invariant behaviour of `evolveHashlifeFast`. -/
theorem evolveHashlifeFastAux_zero_n (fuel : Nat) (g : Grid) :
    evolveHashlifeFastAux fuel 0 g = g := by
  -- The `n = 0` pattern (`| _, 0, g => g`) is the FIRST arm of
  -- `evolveHashlifeFastAux`, so it fires regardless of `fuel`. But `rfl`
  -- fails with `fuel` a free variable: the pattern-matcher inspects `fuel`
  -- first and blocks on the unknown constructor. Splitting on `fuel`
  -- (`0` or `succ`) lets the first arm reduce definitionally in each case.
  cases fuel <;> rfl

/-! ## P5. Main theorem: bounded correctness

The top-level theorem composing P2, P3, P4. -/


/-! ### P5 base case (n = 0)

The trivial case `n = 0`: both `evolveHashlifeFast` and `evolve` return the
grid unchanged. This is the first proven building block toward the full P5
theorem. The remaining work is the inductive step (small `n` fallback + large
`n` jump), documented in `hashlife_correct` below. -/

/-- Base case `n = 0` of `hashlife_correct`: no evolution means no change on
    either side. Both `evolveHashlifeFast 0 g` (via `evolveHashlifeFastAux 0 0 g`)
    and `evolve 0 g` reduce to `g` definitionally. -/
theorem hashlife_correct_base_zero (g : Grid) :
    evolveHashlifeFast 0 g = evolve 0 g := by
  -- evolveHashlifeFast 0 g = evolveHashlifeFastAux 0 0 g = g  (second pattern: 0, _, g => g)
  -- evolve 0 g = g                                           (evolve_zero : rfl)
  rfl

/-! ## P5 inductive step — scaffolding (fallback + jump)

The `sorry` previously sitting at the top of `hashlife_correct` is the second
research-level verrou. It is the **composition** of P4 (central correctness)
with P2 (light-cone) by induction on `n`, with a case split on the MacroCell
level `k` chosen by `box_assez_grand`.

### Proof plan (small-n fallback + large-n jump)

Given `n` and a grid `g` with `box_assez_grand g n`, let `k` be the level
chosen by the predicate (so `c = buildFromGrid k g` is a well-formed level-`k`
cell containing `g` with enough padding). Two cases:

  **Small `n`** (`n < 2^(k-2)`): `evolveHashlifeFast` falls back to `evolve`
  directly — its `evolveHashlifeFastAux` defensive branch delegates to the
  reference step-by-step implementation. Trivially equal. Difficulty: P5.1.

  **Large `n`** (`n ≥ 2^(k-2)`): one Hashlife jump of `2^(k-2)` generations by
  P4 (`hashlifeResult_central_correct`), then recurse on the residual
  `n - 2^(k-2)` generations. The light-cone lemma P2 (`step_light_cone`,
  proven) ensures the boundary of the MacroCell does not interfere with the
  live region during the jump. The padding hypothesis `box_assez_grand` is
  preserved through the recursion (the jump expands the bounding box by at
  most `2^(k-2)`, within the padding margin). Difficulty: P5.2.

### Dependency

`p5_large_n_jump` (P5.2) calls `hashlifeResult_central_correct` (P4) — so P5
is **blocked until P4's inductive step is proven**. But `p5_small_n_fallback`
(P5.1) is independent of P4 and can be proven now. The full
`p5_inductive_step` glues the two cases; it stays `sorry` until both sub-lemmas
are ready.

### Sub-lemmas (difficulty-ranked)

| Lemma | Difficulty | Dependency | What it proves |
|-------|-----------|------------|----------------|
| `p5_small_n_fallback` | P5.1 (definitional) | none | When `n < 2^(k-2)`, `evolveHashlifeFast n g = evolve n g` by the defensive fallback arm |
| `p5_large_n_jump`     | P5.2 (compositional) | **P4** + P2 | When `n ≥ 2^(k-2)`, one P4 jump + light-cone-preserving recursion on `n - 2^(k-2)` |
| `p5_inductive_step`   | P5.3 (glue)         | P5.1 + P5.2 | The full induction on `n`, case-split on `n vs 2^(k-2)` |

See `agent_tests/prover/RUNBOOK.md` for the iteration protocol. -/

/-- **P5.1** (definitional, no P4 dependency): when the number of generations
    `n` is smaller than `jumpSize lvl` (the Hashlife jump size for the grid's
    MacroCell level `lvl`), `evolveHashlifeFast` does not make a recursive
    Hashlife jump — it falls back to the reference `evolve`. This is pure
    definitional unfolding of `evolveHashlifeFastAux`'s small-n arm.

    **PROVEN** (eliminates 1 sorry from the scaffolding). The `zero` case is
    definitional (`evolve 0 g = g`). The `succ k` case splits the guard
    `lvl ≥ 2 && (k+1) ≥ jumpSize lvl`: the guard-true branch contradicts the
    hypothesis `k+1 < jumpSize lvl`, the guard-false branch is the `evolve`
    fallback (definitional equality). -/
theorem p5_small_n_fallback (n : Nat) (g : Grid)
    (h : n < jumpSize (gridToMacroCellWithOffset g).2.level) :
    evolveHashlifeFast n g = evolve n g := by
  show evolveHashlifeFastAux n n g = evolve n g
  cases n with
  | zero => rfl
  | succ k =>
    simp only [evolveHashlifeFastAux]
    split_ifs with hcond
    · -- guard true (jump branch): impossible under h : k+1 < js
      exfalso
      obtain ⟨_hlvl, hnjs⟩ : (gridToMacroCellWithOffset g).2.level ≥ 2 ∧ k + 1 ≥
          jumpSize (gridToMacroCellWithOffset g).2.level := by
        simpa using hcond
      exact absurd hnjs (Nat.not_le_of_lt h)
    · rfl

/-! ### P5.2 obstacle scan (2026-06-15)

**Status after merges #3053 + #3062.** The wf+level structural inputs feeding
`hashlifeResult_central_correct` (L1412) at the P5.2 jump step are now formally
available:

- `wf_padCenter2`    (L1028, PR #3053): `c.wf = true → (padCenter2 c).wf = true`
- `level_padCenter2` (L1031, PR #3062): `1 ≤ c.level → (padCenter2 c).level = c.level + 2`

So when `p5_large_n_jump` eventually invokes the P4 lemma on `padCenter2 c`,
both hypotheses `(hwf : (padCenter2 c).wf = true)` and
`(hk : (padCenter2 c).level = k + 2)` (with `k := c.level`) are dischargeable
from `c.wf = true` and `1 ≤ c.level`. The "wf composition lift residual"
dispatched 2026-06-15 09:59Z is now structurally closed on both axes.

**Residual obstacle chain (3 `sorry` total: L2527, L2855, L2864).**

  `p5_large_n_jump`            (L2852, re-signed to real target — proof body `sorry` at L2855)
    └→ `hashlifeResult_central_correct`  (L2546 — P4 entry point)
         └→ inductive `succ k` arm of P4 — 1 residual `sorry`:
              · wave-glue residual       (L2527, succ-arm composition + assembly)
            (the shape/IH sub-lemmas `p4_double_nine_shape` L1744, `p4_wave1_ih_step`
            L2108, `p4_wave2_ih_step` L2146 carry no `sorry`; the P4.4 half-step
            composition is closed via `evolve_add`/`evolve_half_step` — see note)

The P4 inductive step is **research-level, multi-cycle**. The base case `k = 0`
of P4 is already fully proven (`hashlifeResult_central_correct_base`, L1648,
shape lemmas + `2^16` `native_decide`).

**Note on P4.4 (SUPPRESSED in N2-bis, 2026-07-09).** The standalone
`p4_half_steps_compose` theorem was a `: True` placeholder. Its pure-evolve
half-step content is exactly `evolve_add` (L2353) + `evolve_half_step` (L2370),
both already proven sorry-free; its wave-assembly content is exactly the
wave-glue residual (L2527). Re-signing it would either duplicate L2527 or be
vacuously provable (gaming the sorry count, G.2), so the coordinator greenlit
its **deletion** (sorry 4→3) together with its unused `have _h4` consumer in
`p4_succ_membership`. P4.4 is now carried by `evolve_add`/`evolve_half_step`
(closed) + the L2527 residual.

**N1 frame sub-claim — AUDITED VACUOUS (2026-07-09).** The previously sketched
grain

  `BoxAssezGrand g n → n ≥ jumpSize ... → BoxAssezGrand (jumpResult g) (n - jumpSize ...)`

was audited before proving: its hypotheses are **jointly unsatisfiable on
non-empty grids** (`p5_large_n_hyps_unsat`, proved in the "Structural
satisfiability bound" section above — `BoxAssezGrand g n` caps `n ≤ 2` while
`jumpSize ≥ 8`). Proving it "via decidable evaluation + Nat arithmetic" would
land another vacuous placeholder (the `p4_half_steps_compose` trap, N2-bis).
The frame lemma only becomes meaningful after the `gridFrame`/`box_assez_grand`
satisfiability redesign (design gate, ai-01) — re-scope it then.

**Re-signed target (N2, 2026-07-09).** `p5_large_n_jump` (L2852) now carries the
real conclusion

  `(h : BoxAssezGrand g n) (hbig : n ≥ jumpSize (gridToMacroCellWithOffset g).2.level) →`
  `  evolveHashlifeFast n g = evolve n g`

with the proof body still `sorry` (L2855) pending the P4 unlock. The obstacle
remains structural-on-P4, not local-on-P5. -/

/-- **P5.2 on the FIXED frame — VACUOUS, and therefore closed structurally
    (c.95, ai-01). This lemma carries no operational content.**

    The intent was: when `n ≥ 2^(k-2)`, `evolveHashlifeFast n g` makes one
    Hashlife jump of `2^(k-2)` generations (certified by P4,
    `hashlifeResult_central_correct`), then recurses on `n - 2^(k-2)`.

    **Correction of an earlier claim in this file.** The header above and the
    docstring this replaces both described the lemma as "blocked until P4". That
    was wrong, and the contradiction was already sitting two declarations below:
    `p5_inductive_step` discharges *exactly* this case with `False.elim`. On the
    fixed frame the two hypotheses are jointly unsatisfiable on non-empty grids
    — `BoxAssezGrand g n` caps `n ≤ 2` (`boxAssezGrand_nonempty_le_two`) while
    `hbig` forces `n ≥ 8` (`jumpSize_gridLevel_ge_eight`), whence
    `p5_large_n_hyps_unsat`. No P4 result can ever be needed here, because the
    branch is unreachable. The empty-grid case is separately trivial.

    So the `sorry` that stood here was a **decoy**: it advertised open research
    where there was none, and it could never have been closed by the P4 work it
    pointed at. Replacing it with the explicit vacuity discharge is a *reduction
    in misleading surface*, not a proof of anything — the sorry count drops by
    one while the mathematical content stays at zero, and that has to be said
    out loud rather than banked as progress.

    **The genuine large-`n` target is `p5_large_n_jumpN`** (n-aware frame,
    non-vacuous at `n ≥ 8`, witnessed by `boxAssezGrandN_block_8` /
    `boxAssezGrandN_glider_8`), which remains an open P4-gated sorry. Read that
    one, not this one. -/
theorem p5_large_n_jump (n : Nat) (g : Grid) (h : BoxAssezGrand g n)
    (hbig : n ≥ jumpSize (gridToMacroCellWithOffset g).2.level) :
    evolveHashlifeFast n g = evolve n g := by
  -- **NOT a P4 unlock.** See the docstring: on the fixed frame this statement
  -- is vacuous, and the discharge below is purely structural.
  by_cases hg : g = []
  · -- Empty grid: both sides reduce to `[]` (same unfolding as
    -- `p5_inductive_step`'s empty arm; `hbig` is never used).
    subst hg
    unfold evolveHashlifeFast
    cases n with
    | zero => simp [evolveHashlifeFastAux, evolve]
    | succ k =>
      simp [evolveHashlifeFastAux, gridToMacroCellWithOffset, gridFrame,
            buildFromGrid, MacroCell.level]
  · -- Non-empty grid: `BoxAssezGrand g n` caps `n ≤ 2` while `hbig` forces
    -- `n ≥ 8`. The hypotheses are contradictory.
    exact (p5_large_n_hyps_unsat g n hg h hbig).elim

/-- **P5.3** (glue): the full induction on `n`, with a case split on
    `n < 2^(k-2)` (P5.1) vs `n ≥ 2^(k-2)` (P5.2). Stays `sorry` until both
    sub-lemmas are proven.

    **P5 vacuity analysis (c.307a, 2026-07-10)**: on non-empty grids, the
    hypotheses of the `¬ hsmall` branch are jointly unsatisfiable — see
    `p5_large_n_hyps_unsat` (L425). Concretely:
    - `BoxAssezGrand g n` caps `n ≤ 2` (`boxAssezGrand_nonempty_le_two`,
      proven L358);
    - `n ≥ jumpSize (gridToMacroCellWithOffset g).2.level` requires
      `n ≥ 8` (`jumpSize_gridLevel_ge_eight`, proven L411).
    The conjunction `2 ≤ n ∧ n ≥ 8` is impossible. Hence the large-n arm
    is vacuous on non-empty grids, and `hashlife_correct` would be proven
    if the empty-grid arm (`g = []`) is closed separately (by direct unfold
    of `evolveHashlifeFastAux` on `g = []`, which takes the guard-false
    direct `evolve n g` arm because empty grids yield a level-0 MacroCell
    whose `lvl ≥ 2` guard is false).

    **Honest disclosure**: this vacuity closure is STRUCTURAL, not
    operational. It proves `hashlife_correct` (the bounded correctness
    theorem) WITHOUT actually exercising a Hashlife jump on non-empty
    grids — `box_assez_grand` is too tight (padding margin = 2 cells) to
    allow `n ≥ 8`. The genuine P5.2 jump-step correctness
    (`p5_large_n_jump`, L2999) remains an open sorry, gated on the P4 unlock
    per the section header at L2982. The vacuity closure demonstrates that
    `hashlife_correct`'s STATEMENT is satisfiable on canonical witness
    patterns (`hashlife_correct_implies_block_4` / `_glider_8`), but the
    theorem needs a SATISFIABILITY REDESIGN (`box_assez_grand` → a weaker
    hypothesis that allows `n ≥ 8`) before the genuine P5 jump can be
    proven. -/
theorem p5_inductive_step (n : Nat) (g : Grid) (h : BoxAssezGrand g n) :
    evolveHashlifeFast n g = evolve n g := by
  by_cases hg : g = []
  · -- Empty grid: both sides definitionally `[]`.
    -- `evolveHashlifeFast n [] = evolveHashlifeFastAux n n []`, which unfolds
    -- to `evolve n []` after the `0 >= 2` guard fails on `gridFrame []`'s
    -- level-0 MacroCell. `evolve n []` is `step^[n] []`, and `step [] = []`
    -- via `candidates [] = []`. So both sides are `[]`. The unfolding
    -- reduces to `rfl` after `simp` normalizes the auxiliary definitions.
    subst hg
    unfold evolveHashlifeFast
    cases n with
    | zero => simp [evolveHashlifeFastAux, evolve]
    | succ k =>
      -- `evolveHashlifeFastAux (k+1) (k+1) []` falls into the `fuel+1, n, g`
      -- branch. Inside, `gridToMacroCellWithOffset []` returns a level-0
      -- MacroCell, so `lvl >= 2` is false and we take the else branch
      -- (`evolve (k+1) []`). Lean reduces the `if` since `0 >= 2` is `false`.
      simp [evolveHashlifeFastAux, gridToMacroCellWithOffset, gridFrame,
            buildFromGrid, MacroCell.level]
  · -- Non-empty grid: case-split on `hsmall`.
    by_cases hsmall : n < jumpSize (gridToMacroCellWithOffset g).2.level
    · exact p5_small_n_fallback n g hsmall
    · -- `¬ hsmall` on a non-empty grid: the P5.2 hypotheses are jointly
      -- unsatisfiable (vacuous arm — see `p5_large_n_hyps_unsat`, c.307a
      -- disclosure). Reconstruct `n ≥ jumpSize` and discharge via `False.elim`.
      have hbig : n ≥ jumpSize (gridToMacroCellWithOffset g).2.level :=
        Nat.not_lt.mp hsmall
      exact (p5_large_n_hyps_unsat g n hg h hbig).elim


/-- **Hashlife correctness (bounded)**: under the padding hypothesis
    `box_assez_grand g n`, the exponential-speedup Hashlife implementation
    `evolveHashlifeFast n g` agrees with the reference `evolve n g`.

    **Proof strategy** (P5, difficulty: hard, compositional):
    Induction on `n` with case split on the MacroCell level `k`.
    - Small `n` (n < 2^k): `evolveHashlifeFast` falls back to `evolve`,
      trivially equal.
    - Large `n` (n ≥ 2^k): one jump of `2^k` generations by P4 + recurse on
      the residual `n - 2^k`. The light-cone lemma P2 ensures the boundary
      of the MacroCell doesn't interfere with the live region during the
      jump. The padding hypothesis `box_assez_grand` is preserved through
      the recursion because the jump preserves bounding box up to light-cone
      expansion.

    **Status (2026-06-13)**: base case `n = 0` proven above
    (`hashlife_correct_base_zero`). The inductive step remains open (the
    `sorry` below). See `hashlife_correct_implies_block_4` /
    `hashlife_correct_implies_glider_8` for sanity witnesses. -/
theorem hashlife_correct (n : Nat) (g : Grid) (h : BoxAssezGrand g n) :
    evolveHashlifeFast n g = evolve n g := by
  -- P5 TARGET: main theorem, composition of P2-P4
  -- Base case n = 0: see hashlife_correct_base_zero.
  -- Inductive step (fallback + jump): see p5_inductive_step below.
  exact p5_inductive_step n g h

/-! ## N2 restatement on the n-aware frame — gate W2 (EPIC #3846)

The fixed-frame `hashlife_correct` above is *proven* (via `p5_inductive_step`,
closed #5998), but its hypothesis `BoxAssezGrand g n` is structurally capped at
`n ≤ 2` on non-empty grids (`boxAssezGrand_nonempty_le_two`), while the Hashlife
jump guard requires `n ≥ jumpSize ≥ 8` (`jumpSize_gridLevel_ge_eight`). The
conjunction is unsatisfiable (`p5_large_n_hyps_unsat`), so `hashlife_correct` is
*vacuously true* for the large-`n` regime where the Hashlife jump is actually
exercised — the theorem is proven *without* any genuine jump (the
`p5_inductive_step` non-empty arm discharges via `False.elim` on that unsat
conjunction).

The n-aware restatement `hashlife_correctN` below replaces the hypothesis with
`BoxAssezGrandN g n` (the predicate over `gridFrameN n g`, padding `max 2 n`).
Because `gridFrameN` pads by `max 2 n ≥ n` on every side, `BoxAssezGrandN g n`
is *satisfiable for every `n`* (not just `n ≤ 2`) — witnessed at `n = 8` on
concrete Game-of-Life patterns by `box_assez_grandN_block_8` /
`box_assez_grandN_glider_8` (Bool form, proven above) and the universal
`box_assez_grandN_single_cell`. This makes the large-`n` statement
*non-vacuous*: it is the genuine P5.2 target.

**Anti-gaming (ai-01 gate, msg-...zylpzl).** The restatement carries real value
on the *spec* (a non-vacuous large-`n` correctness statement, witnessed at
`n = 8` on real patterns) and is the honest framing of the remaining work. The
genuine large-`n` Hashlife jump, however, remains an **open named sorry**
`p5_large_n_jumpN` (P5.2, P4-gated) — it is **not** closed by any vacuity
argument, and its body is `sorry` pending the P4 unlock (`p4_succ_membership`,
the offset-matching assembly, ai-01 turf). A gated-meaningful sorry is honest
progress; a vacuous-worthless proof would not be. -/

/-- **Non-vacuity witness, propositional form (gate W2, ai-01 garde-fou 1).**
    `BoxAssezGrandN block 8` holds — the 2×2 still-life carries margin `≥ 8` on
    every side under `gridFrameN 8` (padding `max 2 8 = 8`). This is the
    concrete substrate that makes `hashlife_correctN` non-vacuous at the
    large-`n` regime (vs the fixed-frame `BoxAssezGrand block 8`, unsatisfiable
    by the `n ≤ 2` cap). It is the propositional twin of the Bool-form
    `box_assez_grandN_block 8 = true` (proven above), discharged by
    `native_decide` directly on the `BoxAssezGrandN` proposition via the
    `Decidable (BoxAssezGrandN)` instance. -/
theorem boxAssezGrandN_block_8 : BoxAssezGrandN block 8 := by native_decide

/-- Same non-vacuity witness on the `glider` spaceship at `n = 8`
    (propositional form). -/
theorem boxAssezGrandN_glider_8 : BoxAssezGrandN glider 8 := by native_decide

/-- **P5.2 genuine large-`n` jump (N2, P4-gated) — the sole remaining open
    target of the P5 layer.** When `n ≥ jumpSize k` on the n-aware frame,
    `evolveHashlifeFast` makes one Hashlife jump of `2^(k-2)` generations
    (certified by P4 `hashlifeResult_central_correct`) then recurses
    on `n - 2^(k-2)`, with the light cone staying inside the `gridFrameN` margin
    (`window_cheb_cone_in_domain`, now in `Conway.Life.ConeGeometry`). This is
    the real P5.2 target — **open named sorry, P4-gated** (`p4_succ_membership`,
    ai-01 turf), NOT closed by vacuity.

    **Moved above `hashlife_correctN` (c.95)** so the latter can consume it: the
    N-frame statement is now *derived* from this jump plus the padding-free
    small-`n` fallback, instead of carrying an independent sorry of its own. -/
theorem p5_large_n_jumpN (n : Nat) (g : Grid) (h : BoxAssezGrandN g n)
    (hbig : n ≥ jumpSize (gridToMacroCellWithOffset g).2.level) :
    evolveHashlifeFast n g = evolve n g := by
  sorry

/-- **N2 restatement — the genuine large-`n` correctness statement (EPIC #3846,
    gate W2).** Under the n-aware padding hypothesis `BoxAssezGrandN g n`
    (satisfiable for *every* `n`, unlike `BoxAssezGrand g n` capped at `n ≤ 2`),
    `evolveHashlifeFast n g` agrees with `evolve n g`.

    Unlike the fixed-frame `hashlife_correct` (vacuously true at large `n`),
    this statement is **non-vacuous** at `n ≥ 8` (witnessed by
    `boxAssezGrandN_block_8` / `boxAssezGrandN_glider_8` above).

    **Reduction (c.95, ai-01).** The theorem no longer carries a sorry of its
    own. Splitting on the jump guard discharges it entirely:
    - `n < jumpSize` : `p5_small_n_fallback`, which takes **no padding
      hypothesis whatsoever** — it holds on any frame, the n-aware one included;
    - `n ≥ jumpSize` : `p5_large_n_jumpN`, the genuine P4-gated jump.

    This is a structural reduction, **not** a vacuity closure: the whole
    remaining content of the N-frame statement is now localized in the single
    named sorry `p5_large_n_jumpN`. Before this change the two carried
    independent sorries, and a reader could not tell whether `hashlife_correctN`
    required work *beyond* the jump. It does not. -/
theorem hashlife_correctN (n : Nat) (g : Grid) (h : BoxAssezGrandN g n) :
    evolveHashlifeFast n g = evolve n g := by
  by_cases hsmall : n < jumpSize (gridToMacroCellWithOffset g).2.level
  · exact p5_small_n_fallback n g hsmall
  · exact p5_large_n_jumpN n g h (Nat.not_lt.mp hsmall)

/-- **N3 small-`n` bridge (issue #3846, ai-01 greenlight msg-zx9es2).** On the
    small-`n` regime (`n ≤ 2`), the n-aware spec `BoxAssezGrandN g n` coincides
    with the fixed-frame `BoxAssezGrand g n` (`box_assez_grandN_le_two_eq`), so
    the already-proven `hashlife_correct` discharges the N-version conclusion
    without re-proving it on the n-aware frame.

    Kept after the c.95 reduction of `hashlife_correctN`: it remains an
    *independent* route to the `n ≤ 2` arm, one that goes through the
    **fixed-frame** theorem and never touches `p5_large_n_jumpN` — so it stays
    sorry-free even if the jump is later restated or re-scoped. -/
theorem hashlife_correctN_le_two (n : Nat) (g : Grid) (hn : n ≤ 2)
    (h : BoxAssezGrandN g n) : evolveHashlifeFast n g = evolve n g := by
  apply hashlife_correct n g
  show box_assez_grand g n = true
  rw [← box_assez_grandN_le_two_eq n g hn]
  exact h

/-! ## Sanity witnesses (native_decide)

Concrete instantiations of `hashlife_correct` on small patterns verify that
the theorem is *satisfiable* under the padding hypothesis. Each `native_decide`
here strengthens the scaffolding by confirming the theorem is not vacuous. -/

/-- For the empty grid, any `n` is OK (no live cells to constrain) —
    `List.all` over `[]` is vacuously `true`. -/
example : BoxAssezGrand ([] : Grid) 0 := by
  decide

/-- **Consequence of the strengthen (c.151)**: the strengthened `box_assez_grand`
    only holds for `n ≤ 2` on these canonical patterns, because `gridFrame`
    fixes a 2-cell top/left padding (`r0 := rMin - 2`), so the top margin is
    exactly `2` — `r0 + n ≤ rMin` forces `n ≤ 2`. This is honest geometric
    content (the old vacuous predicate accepted `n = 4, 8` for free). It also
    surfaces a real property of the current `gridFrame`: it under-pads for
    large-`n` correctness, which is material for the P5 plan. -/
example : BoxAssezGrand block 2 := by
  native_decide

/-- The glider (3x3 bounding box) also holds for `n = 2` (its top/left margin
    is the same fixed `2` from `gridFrame`, and its bottom/right margin is
    large enough in the level-`3` frame). -/
example : BoxAssezGrand glider 2 := by
  native_decide

/-- If the theorem is true, then the `native_decide` witnesses must hold.
    This is a "soundness check" — if `hashlife_correct` ever gets proved,
    these follow by specialization. -/
theorem hashlife_correct_implies_block_2
    (H : ∀ n g, BoxAssezGrand g n → evolveHashlifeFast n g = evolve n g) :
    evolveHashlifeFast 2 block = evolve 2 block := by
  have hpad : BoxAssezGrand block 2 := by native_decide
  exact H 2 block hpad

/-- Same soundness check for the glider. -/
theorem hashlife_correct_implies_glider_2
    (H : ∀ n g, BoxAssezGrand g n → evolveHashlifeFast n g = evolve n g) :
    evolveHashlifeFast 2 glider = evolve 2 glider := by
  have hpad : BoxAssezGrand glider 2 := by native_decide
  exact H 2 glider hpad

/-- Period-2 oscillator (horizontal blinker, 3 cells in a row): holds for
    `n = 2` (same fixed-`2` top/left margin from `gridFrame`). -/
example : BoxAssezGrand blinker_h 2 := by
  native_decide

/-- Soundness check for the horizontal blinker. -/
theorem hashlife_correct_implies_blinker_h_2
    (H : ∀ n g, BoxAssezGrand g n → evolveHashlifeFast n g = evolve n g) :
    evolveHashlifeFast 2 blinker_h = evolve 2 blinker_h := by
  have hpad : BoxAssezGrand blinker_h 2 := by native_decide
  exact H 2 blinker_h hpad

/-- Period-2 oscillator (toad, 6 cells in a 4x2 box): holds for `n = 2`. -/
example : BoxAssezGrand toad 2 := by
  native_decide

/-- Soundness check for the toad. -/
theorem hashlife_correct_implies_toad_2
    (H : ∀ n g, BoxAssezGrand g n → evolveHashlifeFast n g = evolve n g) :
    evolveHashlifeFast 2 toad = evolve 2 toad := by
  have hpad : BoxAssezGrand toad 2 := by native_decide
  exact H 2 toad hpad

/-- Period-2 oscillator (beacon, two diagonal blocks in a 4x4 box): holds
    for `n = 2` (bottom/right margin `2` in the level-`3` frame). -/
example : BoxAssezGrand beacon 2 := by
  native_decide

/-- Soundness check for the beacon. -/
theorem hashlife_correct_implies_beacon_2
    (H : ∀ n g, BoxAssezGrand g n → evolveHashlifeFast n g = evolve n g) :
    evolveHashlifeFast 2 beacon = evolve 2 beacon := by
  have hpad : BoxAssezGrand beacon 2 := by native_decide
  exact H 2 beacon hpad

end Life
end Conway
