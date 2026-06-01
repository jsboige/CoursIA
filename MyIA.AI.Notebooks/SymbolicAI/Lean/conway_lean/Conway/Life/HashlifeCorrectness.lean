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
import Conway.Life.MacroCell
import Conway.Life.Hashlife

namespace Conway
namespace Life

open MacroCell

/-! ## P1. Padding predicate

The predicate `box_assez_grand : Grid → Nat → Prop` asserts that the grid's
bounding box, when padded to a MacroCell of level `k`, has at least `n` cells
of margin on every side. This is the "boundary doesn't leak" hypothesis. -/

/-- Manhattan distance between two cells. -/
def manhattan (p q : Int × Int) : Nat :=
  Int.natAbs (p.1 - q.1) + Int.natAbs (p.2 - q.2)

/-- The "light cone" of radius `t` around a cell `p`: all cells within
    Manhattan distance `t`. -/
def lightCone (p : Int × Int) (t : Nat) : List (Int × Int) :=
  -- All cells (r, c) with |r - p.1| + |c - p.2| ≤ t.
  -- Implemented as a list comprehension for decidability.
  let rs := List.range (2 * t + 1) |>.map (fun i => p.1 - (t : Int) + i)
  let cs := List.range (2 * t + 1) |>.map (fun j => p.2 - (t : Int) + j)
  rs.flatMap (fun r => cs.filterMap (fun c =>
    let d := Int.natAbs (r - p.1) + Int.natAbs (c - p.2)
    if d ≤ t then some (r, c) else none))

/-- The bounding box of a grid returns (top-left, side-length), where
    side-length is the smallest power of 2 containing all live cells.
    Returns `((0, 0), 0)` for the empty grid. -/
def gridBoundingBox (g : Grid) : (Int × Int) × Nat :=
  if g.isEmpty then ((0, 0), 0)
  else
    let rMin := g.map (·.1) |>.foldl (fun a b => if a ≤ b then a else b) (g.head!.1)
    let rMax := g.map (·.1) |>.foldl (fun a b => if a ≥ b then a else b) (g.head!.1)
    let cMin := g.map (·.2) |>.foldl (fun a b => if a ≤ b then a else b) (g.head!.2)
    let cMax := g.map (·.2) |>.foldl (fun a b => if a ≥ b then a else b) (g.head!.2)
    let side := Int.natAbs (rMax - rMin) + 1
    let side := max side (Int.natAbs (cMax - cMin) + 1)
    ((rMin, cMin), side)

/-- Helper for `natCeilLog2`: loop doubling `pow` until it reaches `target`.
    Uses explicit fuel to ensure termination. Fuel `target` is sufficient
    since `pow` starts at 1 and doubles each iteration, reaching `target`
    in at most `target` steps (in fact, ⌈log2 target⌉ + 1). -/
def natCeilLog2Loop (fuel : Nat) (target : Nat) (pow : Nat) (k : Nat) : Nat :=
  match fuel with
  | 0 => k  -- fuel exhausted, return current k (defensive default)
  | fuel + 1 =>
    if pow ≥ target then k
    else natCeilLog2Loop fuel target (2 * pow) (k + 1)

/-- Smallest `k` such that `2^k ≥ n`. Returns 0 for n = 0, 1.
    Iterative implementation with bounded fuel (safe upper bound = n + 1). -/
def natCeilLog2 : Nat → Nat
  | 0 => 0
  | n + 1 => natCeilLog2Loop (n + 1) (n + 1) 1 0

/-- The "box assez grand" predicate: the grid's bounding box fits inside a
    MacroCell of level `k`, with at least `n` cells of dead padding on every
    side. This ensures that for `n` generations, no live cell can reach the
    MacroCell boundary (light cone argument).

    Returns the *chosen* level `k` (not just an existential) so that the
    predicate is decidable and `native_decide` can evaluate it on concrete
    grids. -/
def box_assez_grand (g : Grid) (n : Nat) : Bool :=
  let (_, side) := gridBoundingBox g
  let target := side + 2*n
  let k := max 2 (natCeilLog2 target)
  2^k ≥ target && k ≥ 2

/-- Propositional version of `box_assez_grand` for theorem statements. -/
def BoxAssezGrand (g : Grid) (n : Nat) : Prop := box_assez_grand g n = true

instance (g : Grid) (n : Nat) : Decidable (BoxAssezGrand g n) :=
  inferInstanceAs (Decidable (box_assez_grand g n = true))

/-! ## P2. Light-cone locality (speed of light = 1)

The state of cell `p` after `t` generations of B3/S23 depends only on the
initial state of cells within Manhattan distance `t` of `p`. This is the
"speed of light" principle for GoL. -/

/-- If two grids agree on the light cone of radius `t` around `p`, then
    after `t` steps they yield the same liveness at `p`.

    **Proof strategy** (P2, difficulty: intermediate):
    Induction on `t`.
    - Base `t = 0`: `step^0 g = g`, and agreeing on cone of radius 0 means
      agreeing at `p` itself.
    - Inductive step: `step^(t+1) g` at `p` depends only on `step^t g` at
      the Moore neighborhood of `p` (radius 1). By IH, that depends only on
      `g` on cones of radius `t` around each neighbor — union is the cone
      of radius `t+1` around `p`. -/
theorem step_light_cone (t : Nat) (g₁ g₂ : Grid) (p : Int × Int)
    (h_cone : ∀ q ∈ lightCone p t, isAlive g₁ q = isAlive g₂ q) :
    isAlive (evolve t g₁) p = isAlive (evolve t g₂) p := by
  -- P2 TARGET: light-cone locality for B3/S23
  sorry

/-! ## P3. Padding correctness

`padCenter2 c` correctly places `c` at the center of a level-`(k+2)`
MacroCell with `2^k` dead cells of padding on each side. -/

/-- The cells of `padCenter2 c` restricted to the centered region equal
    the cells of `c`.

    **Proof strategy** (P3, difficulty: structural):
    Direct computation. Unfold `padCenter2` (= `padToLevelPlus1` twice),
    unfold `toCellsAux`, observe that the padding `e := emptyOfLevel ...`
    contributes no live cells, and the four copies of `c` are at the same
    position in the centered region. -/
theorem padCenter2_correct (c : MacroCell) :
    let k := c.level
    let padded := padCenter2 c
    let center_off : Int × Int := (2^k, 2^k)
    padded.toCellsAux center_off.1 center_off.2 = c.toCellsAux 0 0 := by
  -- P3 TARGET: structural correctness of padCenter2
  sorry

/-! ## P4. Hashlife central result (decompose-compose)

On a level-`k` MacroCell `c` with adequate padding, `hashlifeResult c`
equals `step^[2^(k-2)]` applied to the centered sub-region.

This is the heart of Hashlife: the recursive quadtree decomposition followed
by memoized recomposition gives the same answer as the flat iteration. -/

/-- For a level-`k` MacroCell `c` with `k ≥ 2`, the centered region of
    `hashlifeResult c` equals `evolve (2^(k-2))` applied to the centered
    region of `c`.

    **Proof strategy** (P4, difficulty: hard, compositional):
    Strong induction on `k`.
    - Base `k = 2`: `hashlifeResult` reduces to `step4x4`, which is the
      direct B3/S23 computation on a 4x4 grid. The centered 2x2 result is
      `step` applied to the 4x4 input (truncated to the center).
    - Inductive step `k → k+1`: the recursive Hashlife makes 9 sub-calls on
      level-`(k-1)` cells, then 4 sub-calls on the resulting level-`(k-1)`
      supercells. Each sub-call uses the IH at level `k-1`. The composition
      matches `step^[2^(k-1)]` by the light-cone lemma P2 applied 2^(k-2)
      times (once per "half-step" in the double-nine decomposition). -/
theorem hashlifeResult_central_correct (c : MacroCell) (k : Nat)
    (hk : c.level = k + 2) :
    let off : Int × Int := (0, 0)
    let result := hashlifeResultAux (k + 2) c
    let expected := evolve (2^k) (c.toGrid off)
    result.toGrid off = expected := by
  -- P4 TARGET: central Hashlife correctness, by induction on level
  sorry

/-! ## P5. Main theorem: bounded correctness

The top-level theorem composing P2, P3, P4. -/

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
      expansion. -/
theorem hashlife_correct (n : Nat) (g : Grid) (h : BoxAssezGrand g n) :
    evolveHashlifeFast n g = evolve n g := by
  -- P5 TARGET: main theorem, composition of P2-P4
  sorry

/-! ## Sanity witnesses (native_decide)

Concrete instantiations of `hashlife_correct` on small patterns verify that
the theorem is *satisfiable* under the padding hypothesis. Each `native_decide`
here strengthens the scaffolding by confirming the theorem is not vacuous. -/

/-- For the empty grid, any `n` is OK (no live cells to evolve). -/
example : BoxAssezGrand ([] : Grid) 0 := by
  decide

/-- The block pattern fits in a level-4 MacroCell with margin for n=4.
    Block has side 2 (4 cells in a 2x2 square), padding for 4 gens needs
    2*4 = 8 cells of margin, so 2 + 8 = 10 ≤ 16 = 2^4. -/
example : BoxAssezGrand block 4 := by
  native_decide

/-- For larger `n`, the padding must be larger too. -/
example : BoxAssezGrand glider 8 := by
  native_decide

/-- If the theorem is true, then the existing `native_decide` witnesses
    must hold. This is a "soundness check" — if `hashlife_correct` ever
    gets proved, these follow by specialization. -/
theorem hashlife_correct_implies_block_4
    (H : ∀ n g, BoxAssezGrand g n → evolveHashlifeFast n g = evolve n g) :
    evolveHashlifeFast 4 block = evolve 4 block := by
  have hpad : BoxAssezGrand block 4 := by native_decide
  exact H 4 block hpad

/-- Same soundness check for the glider. -/
theorem hashlife_correct_implies_glider_8
    (H : ∀ n g, BoxAssezGrand g n → evolveHashlifeFast n g = evolve n g) :
    evolveHashlifeFast 8 glider = evolve 8 glider := by
  have hpad : BoxAssezGrand glider 8 := by native_decide
  exact H 8 glider hpad

end Life
end Conway
