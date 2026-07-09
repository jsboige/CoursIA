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

namespace Conway
namespace Life

open MacroCell

/-! ## P1. Padding predicate

The predicate `box_assez_grand : Grid → Nat → Bool` asserts that every live
cell has at least `n` cells of margin to the MacroCell domain boundary on all
four sides. This is the genuine light-cone "boundary doesn't leak" hypothesis
(strengthened c.151, replacing the vacuous always-true version of c.148). -/

/-- Per-cell light-cone margin check (Bool): the cell `(r,c)` has margin ≥ `n`
    on all four sides of the MacroCell domain `[r0, r0+sz) × [c0, c0+sz)`:
    top `r0+n ≤ r`, bottom `r < r0+sz-n`, left `c0+n ≤ c`, right `c < c0+sz-n`.

    Isolated as a helper taking `r0 c0 sz` as **parameters** (not read from
    `gridFrame`) so that `cellMargin_true_iff` proves cleanly with free
    variables — `decide_eq_true_eq` fires on `decide (r0+n ≤ r)` when `r0` is a
    bound variable, but gets stuck in the `Int.decLe` match when `r0` is the
    non-reducible projection `(gridFrame g).1.1`. This split keeps `mono_n`
    tractable (it bridges through `cellMargin_true_iff`, never unfolding the
    decidability of a symbolic `gridFrame`). -/
def cellMargin (r0 c0 sz : Int) (n : Nat) (r c : Int) : Bool :=
  decide (r0 + n ≤ r) && decide (r < r0 + sz - n) &&
  decide (c0 + n ≤ c) && decide (c < c0 + sz - n)

/-- `cellMargin = true` unfolds to the four `Int` margin bounds as a clean
    propositional conjunction. -/
theorem cellMargin_true_iff (r0 c0 sz : Int) (n : Nat) (r c : Int) :
    cellMargin r0 c0 sz n r c = true ↔
      r0 + n ≤ r ∧ r < r0 + sz - n ∧ c0 + n ≤ c ∧ c < c0 + sz - n := by
  simp only [cellMargin, Bool.and_eq_true, decide_eq_true_eq]
  -- residual is pure `∧`-associativity (left-nested vs flat conjunction)
  tauto

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

/-- The "box assez grand" predicate (light-cone margin, strengthened c.151):
    every live cell of `g` has at least `n` cells of margin to the MacroCell
    domain boundary on all four sides.

    This ensures that over `n` generations, no live cell — and nothing in its
    `n`-step light cone — can reach the MacroCell boundary. The Game of Life
    light cone has radius `n`: each generation, a cell's influence spreads by
    one in Manhattan distance, so over `n` generations a cell can move at most
    `n` towards the boundary. Requiring margin `≥ n` on every side is exactly
    the "boundary doesn't leak" hypothesis the docstring (P1) advertises.

    **Strengthened per ai-01 design-gate decision (a)** (c.148 → c.151): the
    previous definition computed a *fictional* level `k := max 2 (natCeilLog2
    (side + 2*n))` and checked `2^k ≥ target && k ≥ 2`, which is *vacuously
    always-true* (it can always find such a `k`) — see the now-superseded
    `box_assez_grand_always_true` diagnostic. This version instead reads the
    *actual* level `lvl` chosen by `gridFrame g` and checks the genuine
    geometric margin from each live cell to the domain `[r0, r0+2^lvl)²`. It
    is therefore **non-vacuous**: it fails for tight grids / large `n` (see
    `box_assez_grand_not_vacuous`). The `BoxAssezGrand g n` hypothesis in the
    P5 theorems now carries genuine information (ai-01: "equivalence
    conditionnelle"). -/
def box_assez_grand (g : Grid) (n : Nat) : Bool :=
  let ((r0, c0), lvl) := gridFrame g
  let sz : Int := 2^lvl
  -- Every live cell `(r,c)` must satisfy the `cellMargin` bound (margin ≥ n on
  -- all four sides of the MacroCell domain `[r0, r0+sz) × [c0, c0+sz)`).
  g.all (fun (r, c) => cellMargin r0 c0 sz n r c)

/-- Propositional version of `box_assez_grand` for theorem statements. -/
def BoxAssezGrand (g : Grid) (n : Nat) : Prop := box_assez_grand g n = true

instance (g : Grid) (n : Nat) : Decidable (BoxAssezGrand g n) :=
  inferInstanceAs (Decidable (box_assez_grand g n = true))

/-! ### Monotonicity of `box_assez_grand` in the padding parameter

A grid that admits `n` cells of margin also admits any smaller amount `m ≤ n`:
the MacroCell level `lvl` is unchanged (same grid `g`), and each live cell's
four margin bounds only become *weaker* when `n` shrinks (`r0 + m ≤ r0 + n ≤ r`,
and `r < r0 + sz - n ≤ r0 + sz - m`). This is **pure linear arithmetic**
in `n` once `lvl`, `r0`, `c0`, `sz` are fixed. -/

/-- Correctness of `natCeilLog2Loop`: starting from `pow = 2^k`, when the
    fuel budget is sufficient (i.e. `2^(k + fuel) ≥ target`), the loop
    returns some `j` with `2^j ≥ target`. Proof by induction on `fuel`. -/
theorem natCeilLog2Loop_pow_ge :
    ∀ (fuel target pow k : Nat),
      pow = 2 ^ k →
      2 ^ (k + fuel) ≥ target →
      2 ^ natCeilLog2Loop fuel target pow k ≥ target
  | 0, target, _, k, _, hfuel => by
      -- fuel = 0: loop returns k. Have `2^(k + 0) ≥ target`, so `2^k ≥ target`.
      simp only [natCeilLog2Loop, Nat.add_zero] at *
      exact hfuel
  | fuel + 1, target, pow, k, hpow, hfuel => by
      unfold natCeilLog2Loop
      split
      · -- `pow ≥ target`. The loop returns `k`. Use `pow = 2^k`.
        rename_i hpt
        rw [← hpow]; exact hpt
      · -- `pow < target`. Recurse with `fuel`, `2 * pow`, `k + 1`.
        apply natCeilLog2Loop_pow_ge fuel target (2 * pow) (k + 1)
        · -- `2 * pow = 2 * 2^k = 2^(k+1)`.
          rw [hpow, pow_succ]; ring
        · -- `2^((k+1) + fuel) = 2^(k + (fuel + 1)) ≥ target`.
          have heq : k + 1 + fuel = k + (fuel + 1) := by omega
          rw [heq]; exact hfuel

/-- `natCeilLog2 n` returns a `k` with `2^k ≥ n`, i.e. it is a valid
    upper-bounding ceiling logarithm. -/
theorem natCeilLog2_pow_ge (n : Nat) : 2 ^ natCeilLog2 n ≥ n := by
  match n with
  | 0 => simp [natCeilLog2]
  | m + 1 =>
    show 2 ^ natCeilLog2 (m + 1) ≥ m + 1
    unfold natCeilLog2
    apply natCeilLog2Loop_pow_ge (m + 1) (m + 1) 1 0
    · show (1 : Nat) = 2 ^ 0
      simp
    · -- `2^(0 + (m+1)) ≥ m+1`, i.e. `2^(m+1) ≥ m+1`.
      simp only [Nat.zero_add]
      exact Nat.le_of_lt (Nat.lt_two_pow_self)

/-- **Monotonicity of `box_assez_grand` in the padding parameter `n`.**

    If a grid `g` admits `n` cells of light-cone margin (every live cell is ≥ n
    from the MacroCell boundary on all four sides), then it also admits any
    smaller amount `m ≤ n`: the MacroCell level `lvl` is unchanged (same grid),
    and each live cell's four margin bounds only weaken when `n` shrinks
    (`r0 + m ≤ r0 + n ≤ r`, and `r < r0 + sz - n ≤ r0 + sz - m`). -/
theorem box_assez_grand_mono_n (g : Grid) {n m : Nat}
    (h : box_assez_grand g n = true) (hle : m ≤ n) :
    box_assez_grand g m = true := by
  -- Both evaluations share the same `gridFrame g` (hence r0, c0, lvl, sz).
  -- Only the padding shrinks n → m; per-cell, each bound weakens under m ≤ n.
  -- Bridge through `cellMargin_true_iff` to stay at the Prop level (unfolding
  -- the `decide` of a symbolic `gridFrame` projection gets stuck in the
  -- `Int.decLe` match — see the `cellMargin` docstring).
  simp only [box_assez_grand, List.all_eq_true] at h ⊢
  intro x hx
  obtain ⟨r, c⟩ := x
  obtain ⟨h1, h2, h3, h4⟩ :=
    (cellMargin_true_iff _ _ _ _ _ _).mp (h (r, c) hx)
  exact (cellMargin_true_iff _ _ _ _ _ _).mpr
    ⟨by omega, by omega, by omega, by omega⟩

/-- **Non-vacuity (c.148 diagnostic → c.151 strengthen)**: the strengthened
    `box_assez_grand` is NOT always-true — it discriminates on the grid geometry
    and the padding `n`, so the `BoxAssezGrand g n` hypothesis in the P5
    theorems carries genuine information (ai-01: "equivalence conditionnelle").

    A single live cell at `(0,0)` lives in the level-`3` MacroCell frame
    `[-2, 6) × [-2, 6)` (`gridFrame` gives side `5`, `ceilLog2 5 = 3`,
    `2^3 = 8`). Its top margin is `0 - (-2) = 2`, so the predicate holds for
    `n = 2` but fails for `n = 3` (`-2 + 3 = 1 ≰ 0`). This supersedes the c.148
    `box_assez_grand_always_true` diagnostic (removed): the vacuous-always-true
    finding was the *symptom* of the latent defect; this witness is the *proof*
    that the strengthened predicate no longer has it. -/
theorem box_assez_grand_not_vacuous :
    ∃ (g : Grid) (n : Nat), box_assez_grand g n = false := by
  refine ⟨[(0, 0)], 3, ?_⟩
  native_decide

/-- Satisfiability witness: the strengthened predicate holds for the single
    cell at `(0,0)` with `n = 2` (margin exactly `2` on every side). Paired
    with `box_assez_grand_not_vacuous`, this confirms the predicate is neither
    vacuously true nor vacuously false — it carries genuine geometric content. -/
theorem box_assez_grand_single_cell_2 : box_assez_grand [(0, 0)] 2 = true := by
  native_decide

/-! ## P0. Light-cone warm-up lemmas (prover ramp)

Elementary facts about `manhattan` and `lightCone` that feed the **base case**
of P2 (`step_light_cone` at `t = 0`). `manhattan_self` and `manhattan_comm` are
hand-proved here (genuine content — `manhattan` is a metric-like quantity, these
are the reflexivity and symmetry axioms). `self_mem_lightCone` and
`lightCone_zero` are **proved** (PRs #2097, #2107). Originally left as `sorry`
for multi-agent prover warm-up (Epic #1453), both were eliminated by hand
proofs during the prover iteration cycle. -/

/-- The Manhattan distance from a cell to itself is zero. -/
theorem manhattan_self (p : Int × Int) : manhattan p p = 0 := by
  unfold manhattan
  omega

/-- The Manhattan distance is symmetric. -/
theorem manhattan_comm (p q : Int × Int) : manhattan p q = manhattan q p := by
  unfold manhattan
  omega

/-- Every cell lies in its own light cone, for any radius `t`.

    **Proof strategy** (P0, difficulty: easy):
    `manhattan p p = 0 ≤ t` (by `manhattan_self`), so `p` passes the `d ≤ t`
    filter. Unfold `lightCone`; the `i = t` term of `rs` gives
    `p.1 - t + t = p.1` and the `j = t` term of `cs` gives `p.2`, so the pair
    `(p.1, p.2) = p` is produced. Discharge membership over
    `List.flatMap`/`List.filterMap` with `List.mem_flatMap` /
    `List.mem_filterMap`. -/
theorem self_mem_lightCone (p : Int × Int) (t : Nat) : p ∈ lightCone p t := by
  unfold lightCone
  simp only [List.mem_flatMap]
  use p.1
  constructor
  · -- p.1 ∈ rs = (List.range (2*t+1)).map (fun i => p.1 - (t:Int) + i)
    simp only [List.mem_map]
    use t
    constructor
    · simp [List.mem_range]; omega
    · omega  -- p.1 = p.1 - t + t
  · -- p ∈ (List.filterMap ... cs) with r = p.1
    simp only [List.mem_filterMap]
    use p.2
    constructor
    · -- p.2 ∈ cs = (List.range (2*t+1)).map (fun j => p.2 - (t:Int) + j)
      simp only [List.mem_map]
      use t
      constructor
      · simp [List.mem_range]; omega
      · omega  -- p.2 = p.2 - t + t
    · -- filter condition: d = 0 ≤ t, so some (p.1, p.2) = some p
      simp [show (p.1, p.2) = p from rfl]

/-- The light cone of radius `0` is exactly the singleton `[p]`.

    **Proof strategy** (P0, difficulty: easy):
    With `t = 0`, `List.range 1 = [0]`, so `rs = [p.1]` and `cs = [p.2]`; the
    filter keeps `(p.1, p.2)` since `d = 0 ≤ 0`. The whole expression reduces by
    computation — `simp [lightCone]` followed by `decide`, or a direct `List`
    evaluation after `Prod.ext`. -/
theorem lightCone_zero (p : Int × Int) : lightCone p 0 = [p] := by
  simp [lightCone, List.range_succ, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, List.filterMap_cons,
        List.filterMap_nil, Int.natAbs]

/-! ## P2. Light-cone locality (speed of light = 2 in Manhattan distance)

The state of cell `p` after `t` generations of B3/S23 depends only on the
initial state of cells within Manhattan distance `2*t` of `p`. This is the
"speed of light" principle for GoL: in one step, information can travel to
any Moore neighbor (Chebyshev distance 1, Manhattan distance ≤ 2). After
`t` steps, the reachable region has Chebyshev radius `t`, which is contained
in the Manhattan ball of radius `2*t`.

### Helper lemmas for P2

These bridge lemmas establish the locality of a single B3/S23 step, which
is then lifted by induction to `evolve t`. -/

/-- Symmetry of natAbs: `Int.natAbs (a - b) = Int.natAbs (b - a)`. -/
private theorem int_natAbs_sub_comm (a b : Int) :
    Int.natAbs (a - b) = Int.natAbs (b - a) := by
  omega

/-- If `manhattan p q ≤ t`, then `q ∈ lightCone p t`.

    Left as sorry — the proof requires constructing explicit list membership
    witnesses in the `lightCone` comprehension, with `Int.toNat` conversion
    and `Int.natAbs` symmetry. The mathematical fact is trivially true:
    if `|q.1 - p.1| + |q.2 - p.2| ≤ t` then `(q.1, q.2)` is within the
    Manhattan ball of radius `t`, which is exactly what `lightCone p t` enumerates. -/
theorem mem_lightCone_of_manhattan_le (p q : Int × Int) (t : Nat)
    (h : manhattan p q ≤ t) : q ∈ lightCone p t := by
  unfold manhattan at h
  -- h : Int.natAbs (p.1 - q.1) + Int.natAbs (p.2 - q.2) ≤ t
  -- Switch sub order to match lightCone's filterMap predicate (q - p form).
  rw [int_natAbs_sub_comm p.1 q.1, int_natAbs_sub_comm p.2 q.2] at h
  -- h : Int.natAbs (q.1 - p.1) + Int.natAbs (q.2 - p.2) ≤ t
  -- Derive per-coordinate Int bounds via Int.abs_le (omega does not propagate
  -- natAbs through the toNat-cast subgoals reliably).
  have hxNat : Int.natAbs (q.1 - p.1) ≤ t :=
    Nat.le_trans (Nat.le_add_right _ _) h
  have hyNat : Int.natAbs (q.2 - p.2) ≤ t :=
    Nat.le_trans (Nat.le_add_left _ _) h
  have hx_abs : |q.1 - p.1| ≤ (t : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hxNat
  have hy_abs : |q.2 - p.2| ≤ (t : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hyNat
  obtain ⟨hx_lo, hx_hi⟩ := abs_le.mp hx_abs
  obtain ⟨hy_lo, hy_hi⟩ := abs_le.mp hy_abs
  -- Both differences are in [-t, t]; their +t lift is in [0, 2t].
  have hx_nn : (0 : Int) ≤ q.1 - p.1 + (t : Int) := by linarith
  have hy_nn : (0 : Int) ≤ q.2 - p.2 + (t : Int) := by linarith
  -- Witnesses i and j into List.range (2t+1).
  set i : Nat := (q.1 - p.1 + (t : Int)).toNat with hi_def_eq
  set j : Nat := (q.2 - p.2 + (t : Int)).toNat with hj_def_eq
  have hi_cast : (↑i : Int) = q.1 - p.1 + (t : Int) := by
    rw [hi_def_eq]; exact Int.toNat_of_nonneg hx_nn
  have hj_cast : (↑j : Int) = q.2 - p.2 + (t : Int) := by
    rw [hj_def_eq]; exact Int.toNat_of_nonneg hy_nn
  have hi_lt : i < 2 * t + 1 := by
    have h_int : (↑i : Int) < ((2 * t + 1 : Nat) : Int) := by
      rw [hi_cast]; push_cast; linarith
    exact_mod_cast h_int
  have hj_lt : j < 2 * t + 1 := by
    have h_int : (↑j : Int) < ((2 * t + 1 : Nat) : Int) := by
      rw [hj_cast]; push_cast; linarith
    exact_mod_cast h_int
  have hi_image : p.1 - (t : Int) + ↑i = q.1 := by rw [hi_cast]; ring
  have hj_image : p.2 - (t : Int) + ↑j = q.2 := by rw [hj_cast]; ring
  -- Assemble the membership proof.
  -- Note: Lean elaborates `List.range n |>.map (fun i => p.1 - ↑t + i)` (where i : Nat)
  -- as `List.map (fun (i : Int) => p.1 - ↑t + i) (List.range n |>.map (↑·))` —
  -- a composition of two maps. We need two nested `List.mem_map.mpr` calls.
  unfold lightCone
  refine List.mem_flatMap.mpr ⟨q.1, ?_, ?_⟩
  · -- q.1 ∈ List.map (fun (i : Int) => p.1 - ↑t + i) (do let a ← range; pure ↑a)
    refine List.mem_map.mpr ⟨(↑i : Int), ?_, hi_image⟩
    -- ↑i ∈ do let a ← range; pure ↑a — use mem_flatMap on the do/pure form
    refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi_lt, ?_⟩
    exact List.mem_singleton.mpr rfl
  · refine List.mem_filterMap.mpr ⟨q.2, ?_, ?_⟩
    · -- q.2 ∈ List.map (fun (j : Int) => p.2 - ↑t + j) (do let a ← range; pure ↑a)
      refine List.mem_map.mpr ⟨(↑j : Int), ?_, hj_image⟩
      refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj_lt, ?_⟩
      exact List.mem_singleton.mpr rfl
    · -- (if d ≤ t then some (q.1, q.2) else none) = some q
      simp only [if_pos h]

/-- Reverse direction: every cell in `lightCone p t` is within Manhattan
    distance `t` of `p`. The light cone is exactly the Manhattan ball of
    radius `t`. -/
theorem manhattan_le_of_mem_lightCone (p q : Int × Int) (t : Nat)
    (h : q ∈ lightCone p t) : manhattan p q ≤ t := by
  unfold lightCone at h
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_map] at h
  obtain ⟨r, _, c, _, h_some⟩ := h
  by_cases h_le : Int.natAbs (r - p.1) + Int.natAbs (c - p.2) ≤ t
  · rw [if_pos h_le] at h_some
    have h_eq : (r, c) = q := Option.some.inj h_some
    unfold manhattan
    rw [← h_eq]
    rw [int_natAbs_sub_comm p.1 r, int_natAbs_sub_comm p.2 c]
    exact h_le
  · rw [if_neg h_le] at h_some
    simp at h_some

/-- Triangle inequality for Manhattan distance:
    `manhattan p r ≤ manhattan p q + manhattan q r`.
    Used to chain light-cone membership across induction on `evolve` steps. -/
theorem manhattan_triangle (p q r : Int × Int) :
    manhattan p r ≤ manhattan p q + manhattan q r := by
  unfold manhattan
  have h1 : Int.natAbs (p.1 - r.1) ≤ Int.natAbs (p.1 - q.1) + Int.natAbs (q.1 - r.1) := by
    have h_split : p.1 - r.1 = (p.1 - q.1) + (q.1 - r.1) := by ring
    rw [h_split]
    exact Int.natAbs_add_le _ _
  have h2 : Int.natAbs (p.2 - r.2) ≤ Int.natAbs (p.2 - q.2) + Int.natAbs (q.2 - r.2) := by
    have h_split : p.2 - r.2 = (p.2 - q.2) + (q.2 - r.2) := by ring
    rw [h_split]
    exact Int.natAbs_add_le _ _
  omega

/-- Helper: if `a - b` is in the set {-1, 0, 1}, then `Int.natAbs (a - b) ≤ 1`. -/
private theorem int_natAbs_of_three (a b : Int) (h : a - b = -1 ∨ a - b = 0 ∨ a - b = 1) :
    Int.natAbs (a - b) ≤ 1 := by
  rcases h with h | h | h
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide

/-- Every Moore neighbor of `p` has Manhattan distance at most 2 from `p`.
    (Diagonal neighbors have Manhattan distance 2; orthogonal neighbors have 1.)

    **Proof**: For each Moore neighbor `q`, the row difference `p.1 - q.1` and
    column difference `p.2 - q.2` are each in {-1, 0, 1}. By `int_natAbs_of_three`,
    each has `natAbs ≤ 1`, so the Manhattan distance is ≤ 1 + 1 = 2. -/
theorem manhattan_moore_le_two (p q : Int × Int) (hq : q ∈ mooreNeighbors p) :
    manhattan p q ≤ 2 := by
  unfold manhattan mooreNeighbors at *
  simp only [List.mem_cons] at hq
  rcases hq with h | h | h | h | h | h | h | h | h
  · -- q = (p.1-1, p.2-1)
    have hd1 : p.1 - q.1 = 1 := by rw [h]; omega
    have hd2 : p.2 - q.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1-1, p.2)
    have hd1 : p.1 - q.1 = 1 := by rw [h]; omega
    have hd2 : p.2 - q.2 = 0 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1-1, p.2+1)
    have hd1 : p.1 - q.1 = 1 := by rw [h]; omega
    have hd2 : p.2 - q.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1, p.2-1)
    have hd1 : p.1 - q.1 = 0 := by rw [h]; omega
    have hd2 : p.2 - q.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1, p.2+1)
    have hd1 : p.1 - q.1 = 0 := by rw [h]; omega
    have hd2 : p.2 - q.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1+1, p.2-1)
    have hd1 : p.1 - q.1 = -1 := by rw [h]; omega
    have hd2 : p.2 - q.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1+1, p.2)
    have hd1 : p.1 - q.1 = -1 := by rw [h]; omega
    have hd2 : p.2 - q.2 = 0 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q = (p.1+1, p.2+1)
    have hd1 : p.1 - q.1 = -1 := by rw [h]; omega
    have hd2 : p.2 - q.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · -- q ∈ [] — impossible
    simp at h

/-- Moore neighborhood is symmetric: q ∈ mooreNeighbors p → p ∈ mooreNeighbors q.
    Each offset (dr, dc) has its negation (-dr, -dc) in the list. -/
theorem mooreNeighbors_symm (p q : Int × Int)
    (hq : q ∈ mooreNeighbors p) : p ∈ mooreNeighbors q := by
  -- Direct case analysis: for each of the 8 positions of q relative to p,
  -- p appears at the opposite position in mooreNeighbors q.
  unfold mooreNeighbors at *
  simp only [List.mem_cons] at hq
  rcases hq with h | h | h | h | h | h | h | h | h
  · -- q = (p.1-1, p.2-1) → need (p.1, p.2) = (q.1+1, q.2+1) ∈ list
    subst h; simp [Int.sub_add_cancel]
  · -- q = (p.1-1, p.2) → need (p.1, p.2) = (q.1+1, q.2) ∈ list
    subst h; simp [Int.sub_add_cancel]
  · -- q = (p.1-1, p.2+1) → need (p.1, p.2) = (q.1+1, q.2-1) ∈ list
    subst h; simp [Int.sub_add_cancel]
  · -- q = (p.1, p.2-1) → need (p.1, p.2) = (q.1, q.2+1) ∈ list
    subst h; simp [Int.sub_add_cancel]
  · -- q = (p.1, p.2+1) → need (p.1, p.2) = (q.1, q.2-1) ∈ list
    subst h; simp [Int.add_sub_cancel]
  · -- q = (p.1+1, p.2-1) → need (p.1, p.2) = (q.1-1, q.2+1) ∈ list
    subst h; simp [Int.add_sub_cancel]
  · -- q = (p.1+1, p.2) → need (p.1, p.2) = (q.1-1, q.2) ∈ list
    subst h; simp [Int.add_sub_cancel]
  · -- q = (p.1+1, p.2+1) → need (p.1, p.2) = (q.1-1, q.2-1) ∈ list
    subst h; simp
  · simp at h

/-- If `aliveNext g p = true` then `p ∈ candidates g`.
    For survival (S23): `isAlive g p = true` → `p ∈ g`.
    For birth (B3): `liveNeighborCount g p = 3` → some neighbor alive → `p ∈ g.flatMap mooreNeighbors`. -/
theorem aliveNext_true_mem_candidates (g : Grid) (p : Int × Int)
    (h : aliveNext g p = true) : p ∈ candidates g := by
  unfold aliveNext candidates at *
  simp only [List.mem_append]
  -- Split on isAlive g p
  by_cases h_alive : isAlive g p = true
  · -- Survival: p ∈ g (already alive)
    left
    rw [isAlive] at h_alive
    exact Iff.mp (List.elem_iff) h_alive
  · -- Birth: isAlive g p = false, so aliveNext g p = true means liveNeighborCount g p = 3
    -- Then some Moore neighbor q has isAlive g q = true → q ∈ g and p ∈ mooreNeighbors q
    right
    -- Convert h_alive to isAlive g p = false
    have h_iA_false : isAlive g p = false := by
      cases h_iA : isAlive g p
      · rfl
      · exact absurd h_iA h_alive
    -- Derive liveNeighborCount g p = 3 from h (without unfolding isAlive everywhere)
    have h3 : liveNeighborCount g p = 3 := by
      rw [h_iA_false] at h
      -- h : (let n := liveNeighborCount g p; if false then ... else n == 3) = true
      simpa using h
    -- liveNeighborCount unfolds to countP (isAlive g)
    have h_count : (mooreNeighbors p).countP (isAlive g) = 3 := h3
    -- countP = 3 > 0, so exists q ∈ mooreNeighbors p with isAlive g q = true
    have h_pos : 0 < (mooreNeighbors p).countP (isAlive g) := by omega
    rw [List.countP_pos_iff] at h_pos
    obtain ⟨q, hq_mem, hq_alive⟩ := h_pos
    -- hq_alive : isAlive g q (which means isAlive g q = true via Bool coercion)
    -- By symmetry, p ∈ mooreNeighbors q
    have hp_symm : p ∈ mooreNeighbors q := mooreNeighbors_symm p q hq_mem
    -- isAlive g q = true means q ∈ g (elem_iff forward)
    have hq_in_g : q ∈ g := by
      rw [isAlive] at hq_alive
      exact Iff.mp (List.elem_iff) hq_alive
    -- p ∈ g.flatMap mooreNeighbors because q ∈ g and p ∈ mooreNeighbors q
    exact List.mem_flatMap.mpr ⟨q, hq_in_g, hp_symm⟩

/-- Moore neighborhood ⊆ light cone of radius 2. -/
theorem moore_subset_cone (p : Int × Int) (q : Int × Int)
    (hq : q ∈ mooreNeighbors p) : q ∈ lightCone p 2 := by
  have hmd := manhattan_moore_le_two p q hq
  exact mem_lightCone_of_manhattan_le p q 2 hmd

/-- If two grids agree on `p` and all its Moore neighbors, then `aliveNext`
    gives the same result for `p` (B3/S23 locality). -/
theorem aliveNext_local (g₁ g₂ : Grid) (p : Int × Int)
    (h_self : isAlive g₁ p = isAlive g₂ p)
    (h_nbrs : ∀ q ∈ mooreNeighbors p, isAlive g₁ q = isAlive g₂ q) :
    aliveNext g₁ p = aliveNext g₂ p := by
  unfold aliveNext liveNeighborCount
  -- The let-binding creates: if (isAlive g p) then ... else ...
  -- Both sides have the same structure; rewrite with h_self
  rw [h_self]
  -- Now both sides have the same isAlive test; need countP equality
  have h_count : (mooreNeighbors p).countP (isAlive g₁) =
                 (mooreNeighbors p).countP (isAlive g₂) := by
    apply List.countP_congr
    intro q hq
    have h := h_nbrs q hq
    exact iff_of_eq (congrArg (· = true) h)
  rw [h_count]

/-- Bridge: `isAlive (step g) p = aliveNext g p`.
    Since `step g = sortDedup ((candidates g).filter (aliveNext g))` and
    `sortDedup` preserves membership, `p ∈ step g ↔ p ∈ candidates g ∧ aliveNext g p = true`.
    For the forward direction (`aliveNext g p = true → p ∈ step g`), use
    `aliveNext_true_mem_candidates` to obtain `p ∈ candidates g`. -/
theorem isAlive_step_eq_aliveNext (g : Grid) (p : Int × Int) :
    isAlive (step g) p = aliveNext g p := by
  by_cases h : aliveNext g p = true
  · -- aliveNext g p = true case: must have p ∈ step g.
    rw [h]
    unfold isAlive step
    rw [List.elem_iff, mem_sortDedup, List.mem_filter]
    exact ⟨aliveNext_true_mem_candidates g p h, h⟩
  · -- aliveNext g p = false case: p ∉ filter, hence p ∉ step g.
    have h_false : aliveNext g p = false := by
      cases h_iA : aliveNext g p
      · rfl
      · exact absurd h_iA h
    rw [h_false]
    unfold isAlive step
    -- Need: (sortDedup ...).elem p = false. Show p ∉ sortDedup, then elem = false.
    have h_ne : p ∉ sortDedup ((candidates g).filter (aliveNext g)) := by
      rw [mem_sortDedup, List.mem_filter]
      rintro ⟨_, h_alive⟩
      exact h h_alive
    cases h_e : (sortDedup ((candidates g).filter (aliveNext g))).elem p
    · rfl
    · exact absurd (List.elem_iff.mp h_e) h_ne

/-- If two grids agree on the light cone of radius 2 around `p`, then
    `isAlive (step g₁) p = isAlive (step g₂) p` (single-step locality).
    The radius 2 is needed because Moore neighbors (including diagonals)
    have Manhattan distance ≤ 2. -/
theorem step_local (g₁ g₂ : Grid) (p : Int × Int)
    (h_cone : ∀ q ∈ lightCone p 2, isAlive g₁ q = isAlive g₂ q) :
    isAlive (step g₁) p = isAlive (step g₂) p := by
  have h_self : isAlive g₁ p = isAlive g₂ p := by
    apply h_cone p; exact self_mem_lightCone p 2
  have h_nbrs : ∀ q ∈ mooreNeighbors p, isAlive g₁ q = isAlive g₂ q := by
    intro q hq; apply h_cone q; exact moore_subset_cone p q hq
  have h_alive : aliveNext g₁ p = aliveNext g₂ p :=
    aliveNext_local g₁ g₂ p h_self h_nbrs
  rw [isAlive_step_eq_aliveNext, isAlive_step_eq_aliveNext, h_alive]

/-- If two grids agree on the light cone of radius `2 * t` around `p`, then
    after `t` steps they yield the same liveness at `p`.

    The factor of 2 arises because B3/S23's speed of light is 1 in Chebyshev
    distance (= 2 in Manhattan distance for diagonal neighbors). After `t`
    steps, information can travel Chebyshev distance `t`, which is contained
    in the Manhattan ball of radius `2 * t`.

    **Proof strategy** (P2, difficulty: intermediate):
    Induction on `t`.
    - Base `t = 0`: `evolve 0 g = g`, and agreeing on cone of radius 0 means
      agreeing at `p` itself.
    - Inductive step: `evolve (t+1) g = step (evolve t g)`, and `step`
      at `p` depends on `evolve t g` at cells within Manhattan distance 2
      (the Moore neighborhood). By IH, each of those depends on `g` at cells
      within Manhattan distance `2*t` around each neighbor. The union of
      Manhattan balls of radius `2*t` centered on the Moore neighborhood
      (Manhattan distance ≤ 2 from `p`) is the Manhattan ball of radius
      `2*(t+1)` centered on `p`. -/
theorem step_light_cone (t : Nat) (g₁ g₂ : Grid) (p : Int × Int)
    (h_cone : ∀ q ∈ lightCone p (2 * t), isAlive g₁ q = isAlive g₂ q) :
    isAlive (evolve t g₁) p = isAlive (evolve t g₂) p := by
  induction t generalizing p with
  | zero =>
    simp only [evolve_zero, Nat.mul_zero] at *
    exact h_cone p (self_mem_lightCone p 0)
  | succ n ih =>
    simp only [evolve_succ]
    apply step_local
    intro q hq
    apply ih
    intro r hr
    apply h_cone r
    apply mem_lightCone_of_manhattan_le
    have hpq : manhattan p q ≤ 2 := manhattan_le_of_mem_lightCone p q 2 hq
    have hqr : manhattan q r ≤ 2 * n := manhattan_le_of_mem_lightCone q r (2 * n) hr
    have h_tri : manhattan p r ≤ manhattan p q + manhattan q r := manhattan_triangle p q r
    omega

/-! ## Locality composition (radius-doubling agreement)

`evolve_cone_agree` is the sorry-free, P4-independent locality-composition
handle consumed by `p4_succ_membership` (the G3 bridge): it reduces agreement
of `evolve u g₁` and `evolve u g₂` on `lightCone p (2*t)` to agreement of
`g₁ g₂` on the larger `lightCone p (2*(t+u))`, so that a further
`step_light_cone t` step closes the half-step composition. -/

/-- **Locality composition (radius-doubling agreement).** If two grids `g₁ g₂`
    agree on every cell of the light cone of radius `2*(t+u)` around `p`, then
    after evolving each for `u` generations they agree at every point `q` of the
    smaller cone of radius `2*t` around `p`. -/
theorem evolve_cone_agree (t u : Nat) (g₁ g₂ : Grid) (p q : Int × Int)
    (h_cone : ∀ r ∈ lightCone p (2 * (t + u)), isAlive g₁ r = isAlive g₂ r)
    (hq : q ∈ lightCone p (2 * t)) :
    isAlive (evolve u g₁) q = isAlive (evolve u g₂) q := by
  -- `q` sits in `lightCone p (2*t)`. Apply `step_light_cone u` at `q`: it
  -- requires `g₁ g₂` to agree on `lightCone q (2*u)`. For any `r` in that cone,
  -- `manhattan q r ≤ 2*u` and `manhattan p q ≤ 2*t`, so `manhattan p r ≤ 2*(t+u)`
  -- by the triangle inequality, i.e. `r ∈ lightCone p (2*(t+u))`.
  apply step_light_cone u g₁ g₂ q
  intro r hr
  apply h_cone r
  apply mem_lightCone_of_manhattan_le
  have hpq : manhattan p q ≤ 2 * t := manhattan_le_of_mem_lightCone p q (2 * t) hq
  have hqr : manhattan q r ≤ 2 * u := manhattan_le_of_mem_lightCone q r (2 * u) hr
  have htri : manhattan p r ≤ manhattan p q + manhattan q r := manhattan_triangle p q r
  omega

/-! ## P2 corollary. Influence cone (light cone of influence)

`step_light_cone` is the **cone of dependence**: to know the state of `p`
after `t` generations, it suffices to know the cells of `g` within Manhattan
distance `2*t` of `p`. Its contrapositive is the **cone of influence**: a live
cell of `g` outside Manhattan distance `2*t` of `p` cannot make `p` live at
generation `t`. Equivalently, if `p` is live after `t` generations, some live
cell of `g` must lie within Manhattan distance `2*t` — the live region can
expand toward the MacroCell boundary by at most `2*t` per `t` generations.

This is the sorry-free, P4-independent geometric fact underpinning the
`BoxAssezGrand`-preservation argument for P5.2 (the recursion's padding
hypothesis is preserved because the jump of `jumpSize` generations expands the
live region by at most `2*jumpSize`, within the margin `n`). -/

/-- `isAlive` on the empty grid is always `false` (no cell is live). -/
theorem isAlive_empty (p : Int × Int) : isAlive ([] : Grid) p = false := by
  simp [isAlive]

/-- `sortDedup` of the empty list is empty (empty `mergeSort`, empty `dedup`). -/
theorem sortDedup_nil : sortDedup ([] : List (Int × Int)) = [] := by
  simp [sortDedup]

/-- The empty grid is a fixed point of `step` (no live cells → no births). -/
theorem step_empty : step ([] : Grid) = [] := by
  simp [step, candidates, sortDedup_nil]

/-- `evolve` of the empty grid is empty (the fixed point iterated). -/
theorem evolve_empty (t : Nat) : evolve t ([] : Grid) = [] := by
  induction t with
  | zero => simp [evolve_zero]
  | succ k ih => simp [evolve_succ, step_empty, ih]

/-- **Influence cone (contrapositive form)**: if no live cell of `g` lies in
    `lightCone p (2*t)`, then `evolve t g` is dead at `p`. Proof: `g` then
    agrees with the empty grid on the cone, so `step_light_cone` equates
    `evolve t g` to `evolve t ∅` (which is dead everywhere) at `p`.

    This is the directly-usable form for the `BoxAssezGrand`-preservation
    argument: outside the live region (margin ≥ `n`), the cone is all-dead, so
    `evolve t` cannot bring a boundary cell to life within `t < n/2` generations. -/
theorem evolve_dead_of_cone_dead (t : Nat) (g : Grid) (p : Int × Int)
    (h : ∀ q ∈ lightCone p (2 * t), isAlive g q = false) :
    isAlive (evolve t g) p = false := by
  have hagree : ∀ q ∈ lightCone p (2 * t),
      isAlive g q = isAlive ([] : Grid) q := by
    intro q hq
    rw [h q hq, isAlive_empty]
  have heq := step_light_cone t g ([] : Grid) p hagree
  rw [heq, evolve_empty, isAlive_empty]

/-! ## P3. Padding correctness

`padCenter2 c` places `c` (assuming `c.level ≥ 1`) inside a level-`(k+2)`
MacroCell. Each application of `padToLevelPlus1` shifts every cell of
the original input by `+2^(k-1)` (the input lands in the SE position of
the SW sub-quadrant for `nw`, NE/SW/SE wrap analogously). Composing twice,
`padCenter2` shifts every cell of `c` by `+2^(k-1) + 2^k = 3·2^(k-1)`.

To recover `c.toCellsAux 0 0` from `(padCenter2 c).toCellsAux _ _`,
the calling offset must therefore be `-3·2^(k-1)` on both axes. -/

/-- (helper) Empty `MacroCell`s contribute no live cells to the enumeration.
    By induction on the level: at level 0 we have `deadLeaf = leaf false`,
    which `toCellsAux` maps to `[]`; at level `n+1` the four sub-quadrants
    each enumerate to `[]` by the IH, and the concatenation is `[]`. -/
private theorem emptyOfLevel_toCellsAux_eq_nil (n : Nat) (r0 c0 : Int) :
    (MacroCell.emptyOfLevel n).toCellsAux r0 c0 = [] := by
  induction n generalizing r0 c0 with
  | zero => rfl
  | succ n ih =>
    simp only [MacroCell.emptyOfLevel, MacroCell.toCellsAux, ih,
               List.append_nil, List.nil_append]

/-- (helper) `(emptyOfLevel n).level = n` — induction over `n`. -/
private theorem emptyOfLevel_level (n : Nat) : (MacroCell.emptyOfLevel n).level = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show 1 + (MacroCell.emptyOfLevel n).level = n + 1
    rw [ih]; omega

/-- (helper) `padToLevelPlus1` applied to a node-typed `MacroCell` of level
    `1+nw.level` shifts every enumerated cell by `+2^(nw.level)` on both axes.

    By definition of `padToLevelPlus1`, the input `node nw ne sw se` becomes
    `node Q1 Q2 Q3 Q4` where each Qi is a `node` placing the original cell in
    one quadrant (NW for nw, NE for ne, etc.) and `emptyOfLevel nw.level` in
    the others. Empty cells contribute `[]` via `emptyOfLevel_toCellsAux_eq_nil`,
    so only the original cells survive — shifted by `2^nw.level` per axis
    (the inner-quadrant offset). -/
private theorem padToLevelPlus1_toCellsAux_node
    (nw ne sw se : MacroCell) (r0 c0 : Int) :
    (padToLevelPlus1 (MacroCell.node nw ne sw se)).toCellsAux r0 c0
      = (MacroCell.node nw ne sw se).toCellsAux
          (r0 + ((2 ^ nw.level : Nat) : Int))
          (c0 + ((2 ^ nw.level : Nat) : Int)) := by
  have h2s : ((2 ^ (1 + nw.level) : Nat) : Int)
           = ((2 ^ nw.level : Nat) : Int) + ((2 ^ nw.level : Nat) : Int) := by
    push_cast
    rw [Nat.add_comm 1 nw.level, pow_succ]
    ring
  simp only [padToLevelPlus1, MacroCell.toCellsAux, MacroCell.level,
             emptyOfLevel_level, emptyOfLevel_toCellsAux_eq_nil,
             List.nil_append, List.append_nil, h2s, ← Int.add_assoc]

/-- The cells of `padCenter2 c` viewed from the corrected center offset
    equal the cells of `c` viewed from origin. The negative offset
    `-(3·2^(k-1))` exactly cancels the cumulative shift introduced by
    the two `padToLevelPlus1` applications.

    **Statement correction (#2197)**: the previous version used
    `center_off = (2^k, 2^k)`, which is incorrect — it would only cancel
    a shift of `-2^k`, but the actual shift introduced by `padCenter2`
    is `+3·2^(k-1)`. Verified empirically below on the 2×2 block witness
    (`padCenter2_correct_block_level1`).

    **Proof**: case-split on `c`. The leaf case contradicts `hk : 1 ≤ c.level`
    (leaves have level 0). For the node case, apply `padToLevelPlus1_toCellsAux_node`
    twice (the level after one application becomes `1 + nw.level + 1`, so the second
    shift is `2^(1 + nw.level) = 2 · 2^nw.level`). The cumulative shift is
    `2^nw.level + 2·2^nw.level = 3·2^nw.level = 3·2^(c.level - 1)`, which the
    `center_off = -(3·2^(c.level - 1))` exactly cancels. -/
theorem padCenter2_correct (c : MacroCell) (hk : 1 ≤ c.level) :
    let k := c.level
    let padded := padCenter2 c
    let center_off : Int := -(3 * 2 ^ (k - 1) : Int)
    padded.toCellsAux center_off center_off = c.toCellsAux 0 0 := by
  match c, hk with
  | MacroCell.leaf _, hk =>
    -- Leaf level is 0; contradiction with 1 ≤ c.level.
    simp [MacroCell.level] at hk
  | MacroCell.node nw ne sw se, _ =>
    -- c.level = 1 + nw.level, so c.level - 1 = nw.level.
    -- padCenter2 c = padToLevelPlus1 (padToLevelPlus1 c).
    -- After 1st application: shift +2^nw.level. Result level = 2 + nw.level, and its
    -- inner nw is (node e e e nw), with level 1 + nw.level.
    -- After 2nd application: shift +2^(1+nw.level) = 2 · 2^nw.level. Cumulative: 3·2^nw.level.
    simp only [MacroCell.level, padCenter2, Nat.add_sub_cancel_left]
    -- Expose the INNER padToLevelPlus1 as a node literal via rfl (4-way pad form).
    -- This only rewrites the inner occurrence (the outer is padToLevelPlus1 of
    -- a padToLevelPlus1 application, not of a node literal).
    have hinner : padToLevelPlus1 (MacroCell.node nw ne sw se) =
        MacroCell.node
          (MacroCell.node (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level)
                          (MacroCell.emptyOfLevel nw.level) nw)
          (MacroCell.node (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level)
                          ne (MacroCell.emptyOfLevel nw.level))
          (MacroCell.node (MacroCell.emptyOfLevel nw.level) sw
                          (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level))
          (MacroCell.node se (MacroCell.emptyOfLevel nw.level)
                          (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level)) := rfl
    rw [hinner]
    -- Now the outer padToLevelPlus1 is applied to a node literal. Apply shift lemma.
    rw [padToLevelPlus1_toCellsAux_node]
    -- After shift: (node Q1 Q2 Q3 Q4).tCA (c_off + 2^Q1.level) (...) where Q1.level = 1 + nw.level.
    -- Reduce 2^(1+nw.level) = 2^nw.level + 2^nw.level (Int).
    have hpow_succ : ((2 ^ (1 + nw.level) : Nat) : Int)
                   = ((2 ^ nw.level : Nat) : Int) + ((2 ^ nw.level : Nat) : Int) := by
      push_cast
      rw [Nat.add_comm 1 nw.level, pow_succ]
      ring
    -- Unfold the outer toCellsAux + strip empty cells via empty lemmas.
    simp only [MacroCell.toCellsAux, MacroCell.level, emptyOfLevel_level,
               emptyOfLevel_toCellsAux_eq_nil, List.nil_append, List.append_nil, hpow_succ]
    -- Both sides are now 4-way ++ of nw/ne/sw/se applied to Int offsets.
    -- LHS offsets reduce via push_cast + ring to match RHS (-3s + 2s + s = 0; -3s + 2s + 2s = s).
    congr 1
    · congr 1
      · congr 1 <;> push_cast <;> ring_nf
      · congr 1 <;> push_cast <;> ring_nf
    · congr 1 <;> push_cast <;> ring_nf

/-- WITNESS for P3 on a 2×2 block (level 1, shift = 3·2^0 = 3).

    Empirically proven via `native_decide`: the corrected statement
    holds on the level-1 all-alive 2×2 block. This certifies that the
    constant `-(3·2^(k-1))` is correct (vs. the previous `2^k`).

    Future work: extend to general `c.level ≥ 1` by structural argument
    (P3 main theorem above). -/
theorem padCenter2_correct_block_level1 :
    let c : MacroCell :=
      MacroCell.node MacroCell.aliveLeaf MacroCell.aliveLeaf
                     MacroCell.aliveLeaf MacroCell.aliveLeaf
    (padCenter2 c).toCellsAux (-3 : Int) (-3 : Int) = c.toCellsAux 0 0 := by
  native_decide

/-! ## Well-formedness of MacroCells

`MacroCell.level` only walks the `nw` spine, so `c.level = k + 2` does
**not** constrain the `ne`/`sw`/`se` subtrees. `hashlifeResultAux` sends
such malformed cells to its defensive arm (`emptyOfLevel (c.level - 1)`),
while `toGrid`/`evolve` still see the live cells of the misplaced
subtrees — so the unrestricted P4 statement is **false**
(`p4_unrestricted_counterexample` below).

`wf` formalizes the convention stated on the `MacroCell` type ("all
required, by convention but not enforced by the type, to have the same
level"). It is the missing hypothesis of P4. Candidate for promotion to
`Conway.Life.MacroCell` once the P4/P5 proofs land. -/

/-- Well-formed `MacroCell`: every `node` has four well-formed subtrees
    of equal level. Boolean-valued so concrete instances are decidable
    by `decide`/`native_decide`. -/
def MacroCell.wf : MacroCell → Bool
  | .leaf _ => true
  | .node nw ne sw se =>
    nw.wf && ne.wf && sw.wf && se.wf
      && (ne.level == nw.level) && (sw.level == nw.level)
      && (se.level == nw.level)

/-- Separate well-formedness predicate (c.142). An `inductive`, hence OPAQUE
    to defeq — unlike `MacroCell.wf` (a transparent `Bool` def), `cellWf (node …)`
    does NOT whnf-reduce during defeq. This is the unblock for the level/wf
    preservation lemma of `hashlifeResultAux`: its `.wf` conjunct diverges on
    whnf for nested hRA results (any defeq on `(node <hRA terms>).wf` evaluates
    the transparent `wf`, recursing into `hashlifeResultAux`; c.140/c.141, 8M
    heartbeats, 5 formulations). Reformulated over the opaque `cellWf`, the
    conjunct closes by constructor application + `omega` (treating `.level` as
    atoms, as the level conjunct already did). -/
inductive cellWf : MacroCell → Prop
  | leaf (b : Bool) : cellWf (.leaf b)
  | node {nw ne sw se : MacroCell}
      (hnw : cellWf nw) (hne : cellWf ne) (hsw : cellWf sw) (hse : cellWf se)
      (hne_lvl : nw.level = ne.level) (hsw_lvl : nw.level = sw.level)
      (hse_lvl : nw.level = se.level) :
      cellWf (.node nw ne sw se)

/-- Bridge between the opaque `cellWf` predicate and the transparent `MacroCell.wf`
    (c.142). Both directions, by structural induction on `c` (clean context, no
    hRA terms — so no whnf divergence). Lets the preservation lemma consume
    `.wf = true` facts (from `p4_double_nine_shape`, `wf_hashlifeResult_of_level_two`)
    and produce `cellWf`, and lets downstream code convert back. -/
theorem cellWf_of_wf (c : MacroCell) : c.wf = true → cellWf c := by
  induction c with
  | leaf b => intro _; exact cellWf.leaf b
  | node nw ne sw se hnw hne hsw hse =>
    intro h
    have hne_eq : nw.level = ne.level := by simp_all [MacroCell.wf, beq_iff_eq]
    have hsw_eq : nw.level = sw.level := by simp_all [MacroCell.wf, beq_iff_eq]
    have hse_eq : nw.level = se.level := by simp_all [MacroCell.wf, beq_iff_eq]
    have hw_nw : nw.wf = true := by simp_all [MacroCell.wf]
    have hw_ne : ne.wf = true := by simp_all [MacroCell.wf]
    have hw_sw : sw.wf = true := by simp_all [MacroCell.wf]
    have hw_se : se.wf = true := by simp_all [MacroCell.wf]
    exact cellWf.node (hnw hw_nw) (hne hw_ne) (hsw hw_sw) (hse hw_se)
                   hne_eq hsw_eq hse_eq

theorem wf_of_cellWf {c : MacroCell} (h : cellWf c) : c.wf = true := by
  induction h with
  | leaf b => simp [MacroCell.wf]
  | node _ _ _ _ hne_lvl hsw_lvl hse_lvl ihnw ihne ihsw ihse =>
    simp only [MacroCell.wf, ihnw, ihne, ihsw, ihse, ← hne_lvl, ← hsw_lvl, ← hse_lvl,
               beq_self_eq_true, Bool.true_and, Bool.and_true]

/-- A malformed level-2 cell: `nw` is a level-1 node but `ne`/`sw`/`se`
    are bare leaves. `level` only inspects `nw`, so
    `malformedLevel2.level = 2` satisfies the unrestricted P4 hypothesis
    with `k = 0`. Live cells (via `toCellsAux`, which offsets `ne`/`sw`
    by `2^nw.level = 2`): `(1,1)`, `(0,2)`, `(2,0)`. -/
private def malformedLevel2 : MacroCell :=
  .node (.node (leaf false) (leaf false) (leaf false) (leaf true))
        (leaf true) (leaf true) (leaf false)

example : malformedLevel2.level = 2 := rfl
example : malformedLevel2.wf = false := rfl

/-! ## P4. Hashlife central result (decompose-compose)

On a level-`k` MacroCell `c` with adequate padding, `hashlifeResult c`
equals `step^[2^(k-2)]` applied to the centered sub-region.

This is the heart of Hashlife: the recursive quadtree decomposition followed
by memoized recomposition gives the same answer as the flat iteration.

**Statement correction (#2215 followup)**: the previous version used `off =
(0, 0)` for both input and output. This is incorrect: `hashlifeResultAux
(k+2) c` produces a level-`(k+1)` cell representing the centered `2^(k+1) ×
2^(k+1)` region of the level-`(k+2)` input. The center starts at position
`(2^k, 2^k)` in the input's coordinate system. So `result.toGrid (2^k,
2^k)` covers `[2^k, 2^k + 2^(k+1)) × [2^k, 2^k + 2^(k+1))`, which is
exactly the centered region.

**Statement correction (2026-06-11)**: added the `c.wf = true` hypothesis.
Without it the statement is **false**: `c.level = k + 2` only constrains
the `nw` spine, and on malformed cells `hashlifeResultAux` answers
`emptyOfLevel (c.level - 1)` while `evolve` still sees the misplaced live
cells. Certified counterexample: `p4_unrestricted_counterexample`. The
corrected statement is proven in the base case `k = 0` for **all**
well-formed cells (`hashlifeResult_central_correct_base`, 2^16 instances)
and witnessed in the recursive arms at `k = 1` and `k = 2`. -/

/-- Restrict a Grid to the centered region `[lo, lo + size) × [lo, lo + size)`. -/
def restrictGridTo (g : Grid) (lo : Int) (size : Nat) : Grid :=
  g.filter fun p =>
    lo ≤ p.1 && p.1 < lo + (size : Int) &&
    lo ≤ p.2 && p.2 < lo + (size : Int)

/-- **The unrestricted P4 statement is false.** On `malformedLevel2`
    (which satisfies `c.level = 0 + 2`), `hashlifeResultAux` takes its
    defensive malformed arm and returns the empty level-1 cell (LHS
    `= []`), while the reference evolution keeps cell `(1,1)` alive —
    it has exactly two diagonal neighbours, `(0,2)` and `(2,0)`, coming
    from the misplaced leaf subtrees (RHS `= [(1,1)]`). Hence the
    `c.wf` hypothesis in `hashlifeResult_central_correct` is necessary. -/
theorem p4_unrestricted_counterexample :
    ¬ ((hashlifeResultAux (0 + 2) malformedLevel2).toGrid
          ((2 ^ 0 : Nat), (2 ^ 0 : Nat))
        = restrictGridTo (evolve (2 ^ 0) (malformedLevel2.toGrid (0, 0)))
            (2 ^ 0 : Int) (2 ^ (0 + 1))) := by
  native_decide

/-! ## Canonical-form bridge: P4 list equality ⇔ pointwise membership

Both sides of the P4 statement are **canonical** grids
(`Conway.Life.GridCanonical`): the LHS is a `toGrid` (a `sortDedup` image),
the RHS a `filter` of `evolve (2^k)` with `2^k ≥ 1` (a `step` image). By
rigidity of canonical grids (`Canonical.ext`), proving the list equality is
equivalent to proving membership pointwise — which is where the light-cone
(P2) and double-nine decomposition arguments actually live. -/

/-- `toGrid` images are canonical grids. -/
theorem canonical_toGrid (offset : Int × Int) (c : MacroCell) :
    Canonical (c.toGrid offset) := by
  unfold MacroCell.toGrid
  exact canonical_sortDedup _

/-- Membership in a `toGrid` image, unfolded to the raw cell emission. -/
theorem mem_toGrid {c : MacroCell} {offset : Int × Int} {p : Int × Int} :
    p ∈ c.toGrid offset ↔ p ∈ c.toCellsAux offset.1 offset.2 := by
  unfold MacroCell.toGrid
  exact mem_sortDedup

/-- **Offset-shift for `toGrid` membership** (P4.4 offset-matching ingredient).
    Membership of `p` in `c.toGrid (r0, c0)` is equivalent to membership of the
    translated point `(p.1 - r0, p.2 - c0)` in `c.toGrid (0, 0)` — i.e. the cell
    content is the same grid, just viewed at a different origin. This is the
    shift ingredient the P4.4 offset-matching assembly needs to relate each
    quadrant membership `p ∈ out_*.toGrid (off, off)` (after `mem_toGrid_node`
    decomposes the result node into its four children at offsets `(2^k, 2^k)`,
    `(2^k, 2^k + 2^out_nw.level)`, …) to the centered form that
    `centralCorrect_mem` + the ih characterize. -/
theorem mem_toGrid_shift {c : MacroCell} {r0 c0 : Int} {p : Int × Int} :
    p ∈ c.toGrid (r0, c0) ↔ (p.1 - r0, p.2 - c0) ∈ c.toGrid (0, 0) := by
  rw [mem_toGrid, mem_toGrid]
  exact mem_toCellsAux_shift

/-- **Offset-to-offset translation for `toGrid` membership** (P4.4 offset-matching
    ingredient). Membership of `p` in `c.toGrid (a, b)` is equivalent to
    membership of the point translated by `(a'-a, b'-b)` in `c.toGrid (a', b')` —
    i.e. re-anchoring the same cell's grid at a different origin.

    This is the double-shift ingredient the P4.4 offset-matching assembly needs:
    after `mem_toGrid_node` decomposes the result node, each quadrant sits at its
    own offset (e.g. NW at `(2^k, 2^k)`), but `centralCorrect_mem` (G2)
    characterizes the quadrant at offset `(2^(k-1), 2^(k-1))` (its `2^j` centering
    with `j = k-1`). `toGrid_shift_between` bridges those two offsets directly,
    without re-centering through `(0,0)` twice. -/
theorem toGrid_shift_between {c : MacroCell} {a b a' b' : Int} {p : Int × Int} :
    p ∈ c.toGrid (a, b) ↔ (p.1 - a + a', p.2 - b + b') ∈ c.toGrid (a', b') := by
  rw [mem_toGrid_shift]
  constructor
  · intro h
    rw [mem_toGrid_shift]
    have he : (p.1 - a + a' - a', p.2 - b + b' - b') = (p.1 - a, p.2 - b) := by ext <;> ring
    rw [he]; exact h
  · intro h
    rw [mem_toGrid_shift] at h
    have he : (p.1 - a, p.2 - b) = (p.1 - a + a' - a', p.2 - b + b' - b') := by ext <;> ring
    rw [he]; exact h

/-- **G3 infrastructure (toGrid node-decomposition).** Membership in a `node`
    cell's grid decomposes into membership in the four children's grids, with
    the standard quadtree offset shifts (row increases downward, column
    rightward): `nw` at `(r0,c0)`, `ne` at `(r0, c0+half)`, `sw` at
    `(r0+half, c0)`, `se` at `(r0+half, c0+half)`, where `half = 2^nw.level`.

    Pure structural fact — no `hashlifeResultAux`. This is the sorry-free G3
    piece of `p4_succ_membership`: once established, the LHS
    `p ∈ (hashlifeResultAux (k+2) c).toGrid (2^k, 2^k)` (which is a
    `node out_nw out_ne out_sw out_se`) decomposes into the four
    `out_*.toGrid ...` memberships, each characterizable via
    `centralCorrect_mem` + the induction hypothesis `centralCorrect q_* (k-1)`. -/
theorem mem_toGrid_node {nw ne sw se : MacroCell} {r0 c0 : Int} {p : Int × Int} :
    p ∈ (node nw ne sw se).toGrid (r0, c0) ↔
      p ∈ nw.toGrid (r0, c0) ∨
      p ∈ ne.toGrid (r0, c0 + (2 ^ nw.level : Int)) ∨
      p ∈ sw.toGrid (r0 + (2 ^ nw.level : Int), c0) ∨
      p ∈ se.toGrid (r0 + (2 ^ nw.level : Int), c0 + (2 ^ nw.level : Int)) := by
  repeat rw [mem_toGrid]
  simp only [toCellsAux, List.mem_append]
  tauto

/-- **G3 LHS-unlock infrastructure.** The single-step iota reduction of
    `hashlifeResultAux` at the well-formed (`fuel + 1`, 16-grandchild node) arm.

    `hashlifeResultAux`'s definition uses a pattern alias `c@(node ...)`, whose
    alias fvar blocks `simp`/`unfold` syntactic rewriting (cf. the
    `HashlifeMemo` comment). This lemma restates the well-formed arm with
    explicit patterns and zeta-expanded `let`s, so it IS available for
    rewriting from this module. It is true by `rfl` (iota + zeta reduction).

    **Why this is the LHS-unlock for `p4_succ_membership`**: the goal's LHS is
    `p ∈ (hashlifeResultAux (k+2) c).toGrid (2^k, 2^k)`. With `k+2 = (k+1)+1`
    and `c` destructured via `p4_double_nine_shape`, this lemma rewrites the
    `hRA` application to the explicit `node out_nw out_ne out_sw out_se` (else
    branch, level ≥ 3), exposing the `node _ _ _ _` constructor that
    `mem_toGrid_node` needs. It is the missing link between the LHS and the
    G3 toGrid decomposition. -/
theorem hashlifeResultAux_succ_node (fuel : Nat)
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell) :
    hashlifeResultAux (fuel + 1)
      (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
            (node c1 c2 c3 c4) (node d1 d2 d3 d4)) =
    if (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).level == 2 then
      step4x4 (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                    (node c1 c2 c3 c4) (node d1 d2 d3 d4))
    else
      node
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a1 a2 a3 a4))
          (hashlifeResultAux fuel (node a2 b1 a4 b3))
          (hashlifeResultAux fuel (node a3 a4 c1 c2))
          (hashlifeResultAux fuel (node a4 b3 c2 d1))))
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a2 b1 a4 b3))
          (hashlifeResultAux fuel (node b1 b2 b3 b4))
          (hashlifeResultAux fuel (node a4 b3 c2 d1))
          (hashlifeResultAux fuel (node b3 b4 d1 d2))))
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a3 a4 c1 c2))
          (hashlifeResultAux fuel (node a4 b3 c2 d1))
          (hashlifeResultAux fuel (node c1 c2 c3 c4))
          (hashlifeResultAux fuel (node c2 d1 c4 d3))))
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a4 b3 c2 d1))
          (hashlifeResultAux fuel (node b3 b4 d1 d2))
          (hashlifeResultAux fuel (node c2 d1 c4 d3))
          (hashlifeResultAux fuel (node d1 d2 d3 d4)))) := rfl

/-- Membership in a restricted grid: in the grid and inside the window. -/
theorem mem_restrictGridTo {g : Grid} {lo : Int} {size : Nat} {p : Int × Int} :
    p ∈ restrictGridTo g lo size ↔
      p ∈ g ∧ lo ≤ p.1 ∧ p.1 < lo + (size : Int) ∧
        lo ≤ p.2 ∧ p.2 < lo + (size : Int) := by
  simp [restrictGridTo, List.mem_filter, and_assoc]

/-- **Four-quadrant window partition** (P4.4 offset-matching ingredient, G1).
    A square window `[a, a + 2s)²` (with `0 ≤ s`) is exactly the disjoint union
    of its four half-side quadrants: NW `[a, a+s)²`, NE `[a, a+s) × [a+s, a+2s)`,
    SW `[a+s, a+2s) × [a, a+s)`, SE `[a+s, a+2s)²`. Pure linear arithmetic — no
    `hashlifeResultAux`, no whnf.

    This is the G1 ingredient the `p4_succ_membership` offset-matching assembly
    consumes: the RHS window bounds `[2^k, 2^k + 2^(k+1))² = [2^k, 3·2^k)²`
    (from `mem_restrictGridTo`, with `lo = 2^k`, `size = 2^(k+1)`) factor as
    `[a, a+2s)²` with `a = 2^k`, `s = 2^k`; the four quadrants of the result node
    (each level `k`, side `2^k = s`) tile exactly these four sub-windows. The
    disjunction `Or` on the LHS (from `mem_toGrid_node`) thus partitions the
    window bound on the RHS. -/
theorem quad_partition_bounds (a s : Int) (hs : 0 ≤ s) (p : Int × Int) :
    (a ≤ p.1 ∧ p.1 < a + 2*s ∧ a ≤ p.2 ∧ p.2 < a + 2*s) ↔
      (a ≤ p.1 ∧ p.1 < a + s ∧ a ≤ p.2 ∧ p.2 < a + s) ∨
      (a ≤ p.1 ∧ p.1 < a + s ∧ a + s ≤ p.2 ∧ p.2 < a + 2*s) ∨
      (a + s ≤ p.1 ∧ p.1 < a + 2*s ∧ a ≤ p.2 ∧ p.2 < a + s) ∨
      (a + s ≤ p.1 ∧ p.1 < a + 2*s ∧ a + s ≤ p.2 ∧ p.2 < a + 2*s) := by
  omega

/-- **The P4 ext bridge**: pointwise membership suffices for the P4 goal.
    Reduces the list-equality statement of `hashlifeResult_central_correct`
    to a per-cell biconditional. -/
theorem p4_ext_bridge (c : MacroCell) (k : Nat)
    (h : ∀ p, p ∈ (hashlifeResultAux (k + 2) c).toGrid ((2^k : Nat), (2^k : Nat)) ↔
        p ∈ restrictGridTo (evolve (2^k) (c.toGrid (0, 0))) (2^k : Int) (2^(k+1))) :
    (hashlifeResultAux (k + 2) c).toGrid ((2^k : Nat), (2^k : Nat)) =
      restrictGridTo (evolve (2^k) (c.toGrid (0, 0))) (2^k : Int) (2^(k+1)) := by
  apply Canonical.ext (canonical_toGrid _ _) _ h
  unfold restrictGridTo
  exact (canonical_evolve_of_pos (Nat.two_pow_pos k) _).filter _

/-! ## P4 base case, proven in general

The base case `k = 0` of the (corrected) P4 statement, proven for **all**
well-formed level-2 cells — not just the witnesses above. The shape
lemmas reduce a well-formed level-2 cell to its 16 leaf booleans; the
exhaustive lemma then checks all `2^16` configurations by
`native_decide`. This certifies that the corrected statement is
*provable* (at least in the base case), not merely satisfiable. -/

/-- A level-0 cell is a leaf (regardless of well-formedness). -/
private theorem shape_of_level_zero :
    ∀ c : MacroCell, c.level = 0 → ∃ b, c = leaf b
  | leaf b, _ => ⟨b, rfl⟩
  | node _ _ _ _, h => by exfalso; simp only [MacroCell.level] at h; omega

/-- A level-`(n+1)` cell is a node whose `nw` has level `n`. -/
private theorem shape_of_level_succ :
    ∀ (c : MacroCell) (n : Nat), c.level = n + 1 →
      ∃ nw ne sw se, c = node nw ne sw se ∧ nw.level = n
  | leaf _, _, h => by exfalso; simp only [MacroCell.level] at h; omega
  | node nw ne sw se, n, h =>
    ⟨nw, ne, sw, se, rfl, by simp only [MacroCell.level] at h; omega⟩

/-- Unpack the well-formedness of a node: four well-formed subtrees of
    equal level. -/
private theorem wf_node_elim {nw ne sw se : MacroCell}
    (h : (node nw ne sw se).wf = true) :
    nw.wf = true ∧ ne.wf = true ∧ sw.wf = true ∧ se.wf = true
      ∧ ne.level = nw.level ∧ sw.level = nw.level ∧ se.level = nw.level := by
  simp only [MacroCell.wf, Bool.and_eq_true, beq_iff_eq] at h
  tauto

/-- Combine a node's `level` and `wf` hypotheses to extract the **absolute**
    level (not merely equality) and well-formedness of all four quadrants.
    `wf_node_elim` yields only relative level equality (`ne.level = nw.level`
    etc.); this lemma closes the gap by folding in `(node nw ne sw se).level
    = n + 1` to pin each quadrant's level to `n`. This is the depth-1
    ingredient of the P4 double-nine decomposition (`p4_double_nine_shape`),
    which needs every depth-2 sub-component of a well-formed level-`(k+2)`
    cell to carry a known level `k`. Reusable wherever a well-formed node's
    quadrant levels must be pinned to an absolute value rather than a spine
    offset. -/
private theorem wf_node_quad_level {nw ne sw se : MacroCell} {n : Nat}
    (hlevel : (node nw ne sw se).level = n + 1)
    (hwf : (node nw ne sw se).wf = true) :
    nw.level = n ∧ ne.level = n ∧ sw.level = n ∧ se.level = n ∧
      nw.wf = true ∧ ne.wf = true ∧ sw.wf = true ∧ se.wf = true := by
  obtain ⟨hnw, hne, hsw, hse, hne_eq, hsw_eq, hse_eq⟩ := wf_node_elim hwf
  simp only [MacroCell.level] at hlevel
  refine ⟨?_, ?_, ?_, ?_, hnw, hne, hsw, hse⟩
  all_goals omega

/-- Constructor counterpart to `wf_node_quad_level` (#3012): where that lemma
    *projects* a node's four quadrants, this one *builds* a well-formed node from
    four equal-level well-formed cells, concluding both `level = n + 1` and
    `wf = true`. The second depth-1 ingredient of `p4_double_nine_shape` (P4.1):
    every double-nine sub-cell `n_i` is a `node` of four grandchildren of `c`,
    so once the grandchildren are pinned (by `wf_node_depth2_grandchildren`
    below), this helper closes each sub-cell's `level = k + 1 ∧ wf = true`. -/
private theorem node_wf_level_of_four {g1 g2 g3 g4 : MacroCell} {n : Nat}
    (h1 : g1.level = n) (h2 : g2.level = n) (h3 : g3.level = n) (h4 : g4.level = n)
    (hw1 : g1.wf = true) (hw2 : g2.wf = true) (hw3 : g3.wf = true) (hw4 : g4.wf = true) :
    (node g1 g2 g3 g4).level = n + 1 ∧ (node g1 g2 g3 g4).wf = true := by
  refine ⟨?_, ?_⟩
  · show 1 + g1.level = n + 1
    rw [h1]; omega
  · show (g1.wf && g2.wf && g3.wf && g4.wf
            && (g2.level == g1.level) && (g3.level == g1.level) && (g4.level == g1.level)) = true
    rw [hw1, hw2, hw3, hw4, h1, h2, h3, h4]
    simp only [Bool.true_and, Bool.and_true, beq_self_eq_true]

/-- Depth-2 lift of `wf_node_quad_level` (#3012): a well-formed level-`(n + 2)`
    node has all sixteen depth-2 grandchildren at level `n` and well-formed.
    Applying `wf_node_quad_level` to the outer node pins its four quadrants to
    level `n + 1`; applying it once more to each quadrant pins the sixteen
    grandchildren to level `n`. This is the structural fact
    `p4_double_nine_shape` (P4.1) needs: the nine double-nine sub-cells are
    `node`s of four grandchildren each (see the `n1`..`n9` pattern in
    `Hashlife.lean`'s `hashlifeResultAux`), so combined with
    `node_wf_level_of_four` this discharges every sub-cell's
    `level = k + 1 ∧ wf = true`, leaving only the tiling-union half of P4.1. -/
private theorem wf_node_depth2_grandchildren
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (n : Nat)
    (hlevel : (node (node nw_nw nw_ne nw_sw nw_se)
                    (node ne_nw ne_ne ne_sw ne_se)
                    (node sw_nw sw_ne sw_sw sw_se)
                    (node se_nw se_ne se_sw se_se)).level = n + 2)
    (hwf : (node (node nw_nw nw_ne nw_sw nw_se)
                 (node ne_nw ne_ne ne_sw ne_se)
                 (node sw_nw sw_ne sw_sw sw_se)
                 (node se_nw se_ne se_sw se_se)).wf = true) :
    nw_nw.level = n ∧ nw_nw.wf = true ∧
    nw_ne.level = n ∧ nw_ne.wf = true ∧
    nw_sw.level = n ∧ nw_sw.wf = true ∧
    nw_se.level = n ∧ nw_se.wf = true ∧
    ne_nw.level = n ∧ ne_nw.wf = true ∧
    ne_ne.level = n ∧ ne_ne.wf = true ∧
    ne_sw.level = n ∧ ne_sw.wf = true ∧
    ne_se.level = n ∧ ne_se.wf = true ∧
    sw_nw.level = n ∧ sw_nw.wf = true ∧
    sw_ne.level = n ∧ sw_ne.wf = true ∧
    sw_sw.level = n ∧ sw_sw.wf = true ∧
    sw_se.level = n ∧ sw_se.wf = true ∧
    se_nw.level = n ∧ se_nw.wf = true ∧
    se_ne.level = n ∧ se_ne.wf = true ∧
    se_sw.level = n ∧ se_sw.wf = true ∧
    se_se.level = n ∧ se_se.wf = true := by
  have ho := wf_node_quad_level hlevel hwf
  obtain ⟨q1l, q2l, q3l, q4l, q1w, q2w, q3w, q4w⟩ := ho
  have hnw := wf_node_quad_level (n := n) q1l q1w
  obtain ⟨a1, a2, a3, a4, b1, b2, b3, b4⟩ := hnw
  have hne := wf_node_quad_level (n := n) q2l q2w
  obtain ⟨c1, c2, c3, c4, d1, d2, d3, d4⟩ := hne
  have hsw := wf_node_quad_level (n := n) q3l q3w
  obtain ⟨e1, e2, e3, e4, f1, f2, f3, f4⟩ := hsw
  have hse := wf_node_quad_level (n := n) q4l q4w
  obtain ⟨g1, g2, g3, g4, h1', h2', h3', h4'⟩ := hse
  exact ⟨a1, b1, a2, b2, a3, b3, a4, b4,
         c1, d1, c2, d2, c3, d3, c4, d4,
         e1, f1, e2, f2, e3, f3, e4, f4,
         g1, h1', g2, h2', g3, h3', g4, h4'⟩

/-! ## P3/P4 structural input: empty + padding level/wf preservation

`emptyOfLevel`, `padToLevelPlus1`, `padCenter2`, and `centerInLevelPlus2`
build larger well-formed cells from smaller ones, used by P3 (frame
correctness) and P4 (centering before the Hashlife result). The level and
well-formedness of these results are structural inputs to both pillars:
P3's frame lemma and P4's centering both presuppose the padded cell is
well-formed at the expected level. The `emptyOfLevel_wf` and
`padToLevelPlus1` level+wf facts below are the foundational steps;
`padCenter2`/`centerInLevelPlus2` lift by composition. -/

/-- `(emptyOfLevel n)` is well-formed — induction over `n`. The base case
    `n = 0` is `deadLeaf.wf = true` (a leaf). The successor case: four
    equal-level wf subtrees (each `emptyOfLevel n`, wf by IH, same level by
    `emptyOfLevel_level`), so the node's `wf` conjunction holds. -/
private theorem emptyOfLevel_wf (n : Nat) : (MacroCell.emptyOfLevel n).wf = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (MacroCell.node (MacroCell.emptyOfLevel n) (MacroCell.emptyOfLevel n)
              (MacroCell.emptyOfLevel n) (MacroCell.emptyOfLevel n)).wf = true
    simp only [MacroCell.wf, Bool.and_eq_true, beq_iff_eq, ih, emptyOfLevel_level]
    trivial

/-- `padToLevelPlus1 (node nw ne sw se)` has level `1 + nw.level + 1`: its
    `nw` sub-cell `(node e e e nw)` has level `1 + e.level = 1 + nw.level`
    (since `e = emptyOfLevel nw.level`), so the outer node has level
    `1 + (1 + nw.level)`. -/
private theorem level_padToLevelPlus1 {nw ne sw se : MacroCell} :
    (padToLevelPlus1 (node nw ne sw se)).level = 1 + nw.level + 1 := by
  simp only [padToLevelPlus1, MacroCell.level, emptyOfLevel_level]
  omega

/-- `padToLevelPlus1` preserves well-formedness: from a well-formed node it
    produces a well-formed node one level higher. Each of the four sub-cells
    `(node e e e nw)` etc. is well-formed (three wf equal-level empties plus
    one original subtree) at the same level `1 + nw.level`, so the outer
    node's `wf` conjunction holds. -/
private theorem wf_padToLevelPlus1 {nw ne sw se : MacroCell}
    (h : (node nw ne sw se).wf = true) :
    (padToLevelPlus1 (node nw ne sw se)).wf = true := by
  obtain ⟨hwa, hwb, hwd, hwe, hla, hlb, hld⟩ := wf_node_elim h
  -- emptyOfLevel nw.level : wf, level = nw.level
  have he_wf : (MacroCell.emptyOfLevel nw.level).wf = true := emptyOfLevel_wf nw.level
  have he_lvl : (MacroCell.emptyOfLevel nw.level).level = nw.level := emptyOfLevel_level nw.level
  -- The 4 outer sub-cells are all (node e e e nw) etc. Each has level 1+nw.level
  -- and is wf (3 empties + 1 original, all wf, all equal-level). Build wf directly.
  show (MacroCell.node
          (MacroCell.node (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level)
                          (MacroCell.emptyOfLevel nw.level) nw)
          (MacroCell.node (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level)
                          ne (MacroCell.emptyOfLevel nw.level))
          (MacroCell.node (MacroCell.emptyOfLevel nw.level) sw
                          (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level))
          (MacroCell.node se (MacroCell.emptyOfLevel nw.level)
                          (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level))).wf = true
  simp only [MacroCell.wf, Bool.and_eq_true, beq_iff_eq]
  -- each inner node's wf: 3 empties (wf, same level) + 1 original (wf by hwa/etc.)
  -- and inner level equality (1 + nw.level everywhere)
  simp only [MacroCell.wf, Bool.and_eq_true, beq_iff_eq, he_wf, hwa, hwb, hwd, hwe,
             MacroCell.level, he_lvl, hla, hlb, hld]
  decide

/-- `padToLevelPlus1` preserves well-formedness in either arm: a leaf passes
    through unchanged (`MacroCell.wf (.leaf _) = true`), and a node is padded
    into a wf node by `wf_padToLevelPlus1`. General (non-destructured) form so
    it composes, closing the gap that the destructured `{nw ne sw se}` form
    leaves for the leaf case. -/
private theorem wf_padToLevelPlus1_gen (c : MacroCell) (h : c.wf = true) :
    (padToLevelPlus1 c).wf = true := by
  cases c with
  | leaf _ => simp only [padToLevelPlus1, MacroCell.wf]
  | node nw ne sw se => exact wf_padToLevelPlus1 h

/-- **`padCenter2` preserves well-formedness** — the composition of the two
    `padToLevelPlus1` steps. `padCenter2` is definitionally
    `padToLevelPlus1 (padToLevelPlus1 c)` (Hashlife.lean); this lemma delivers
    the wf lift-by-composition advertised alongside `padToLevelPlus1` /
    `centerInLevelPlus2`. P5.2 structural input: `hashlifeJump c =
    hashlifeResult (padCenter2 c)` feeds `hashlifeResult_central_correct`,
    whose hypothesis `c.wf = true` requires `(padCenter2 c).wf = true` on the
    padded input. -/
theorem wf_padCenter2 (c : MacroCell) (h : c.wf = true) :
    (padCenter2 c).wf = true := by
  show (padToLevelPlus1 (padToLevelPlus1 c)).wf = true
  exact wf_padToLevelPlus1_gen _ (wf_padToLevelPlus1_gen c h)

/-- **`padCenter2` lifts the level by 2** (level companion of
    `wf_padCenter2`). On a node `c` (hence `1 ≤ c.level`), composing
    `padToLevelPlus1` twice raises the level by exactly 2: inner pad
    yields `c.level + 1`, outer pad of the resulting node yields
    `c.level + 2`. Mirrors the destructured `level_padToLevelPlus1`
    (L974) but in the consumer-friendly form `(hk : 1 ≤ c.level)`, same
    shape as `padCenter2_correct` (L636) so they chain. Closes the
    level-side of the `padCenter2` lift advertised alongside
    `wf_padCenter2`. -/
theorem level_padCenter2 (c : MacroCell) (hk : 1 ≤ c.level) :
    (padCenter2 c).level = c.level + 2 := by
  cases c with
  | leaf b =>
    -- leaves have level 0, contradicting 1 ≤ c.level
    simp only [MacroCell.level] at hk
    omega
  | node nw ne sw se =>
    show (padToLevelPlus1 (padToLevelPlus1
            (MacroCell.node nw ne sw se))).level
          = (MacroCell.node nw ne sw se).level + 2
    simp only [padToLevelPlus1, MacroCell.level, emptyOfLevel_level]
    omega

/-! ## P4 structural input: centerInLevelPlus2 level + wf

`centerInLevelPlus2 c` embeds `c` (any level `n`) in a level-`(n+2)` cell,
one copy of `c` per quadrant, the rest all-dead padding of level `n`. This
is the centering helper P4 calls before running `hashlifeResult` on the
padded cell. Its level and well-formedness are P4 structural inputs: the
level-`(n+2)` shape is what makes `box_assez_grand` + the centered
`toGrid (2^k, 2^k)` window meaningful, and the well-formedness is the
missing hypothesis of P4 (the algorithm's well-formed arm). -/

/-- `centerInLevelPlus2 c` has level `c.level + 2`: its `nw` sub-cell
    `(node e e e c)` has level `1 + e.level = 1 + c.level` (with
    `e = emptyOfLevel c.level`), so the outer node has level
    `1 + (1 + c.level)`. -/
theorem level_centerInLevelPlus2 (c : MacroCell) :
    (centerInLevelPlus2 c).level = c.level + 2 := by
  show (MacroCell.node
          (MacroCell.node (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level)
                          (MacroCell.emptyOfLevel c.level) c)
          (MacroCell.node (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level)
                          c (MacroCell.emptyOfLevel c.level))
          (MacroCell.node (MacroCell.emptyOfLevel c.level) c
                          (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level))
          (MacroCell.node c (MacroCell.emptyOfLevel c.level)
                          (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level))).level
        = c.level + 2
  simp only [MacroCell.level, emptyOfLevel_level]
  omega

/-- `centerInLevelPlus2` preserves well-formedness: from a well-formed `c`
    it produces a well-formed level-`(c.level+2)` cell. Each quadrant is
    `(node e e e c)` (or a rotation) — three wf equal-level empties plus
    `c` (wf, same level `c.level`), so all four quadrants are wf at the same
    level `1 + c.level`, and the outer node's `wf` conjunction holds. -/
theorem wf_centerInLevelPlus2 (c : MacroCell) (h : c.wf = true) :
    (centerInLevelPlus2 c).wf = true := by
  show (MacroCell.node
          (MacroCell.node (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level)
                          (MacroCell.emptyOfLevel c.level) c)
          (MacroCell.node (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level)
                          c (MacroCell.emptyOfLevel c.level))
          (MacroCell.node (MacroCell.emptyOfLevel c.level) c
                          (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level))
          (MacroCell.node c (MacroCell.emptyOfLevel c.level)
                          (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level))).wf
        = true
  simp only [MacroCell.wf, Bool.and_eq_true, beq_iff_eq]
  simp only [MacroCell.wf, Bool.and_eq_true, beq_iff_eq,
             emptyOfLevel_wf, h, MacroCell.level, emptyOfLevel_level]
  decide

/-! ## P4 structural input: step4x4 shape

`step4x4` is the Hashlife base case (level-2 input -> one generation). It
always returns a level-1 cell, unconditionally: in the `level == 2` arm it
returns `node (leaf _) (leaf _) (leaf _) (leaf _)`, and in the `else` arm it
returns `emptyOfLevel 1`. This level-1 shape is a structural input to the
`hashlifeResult` level-preservation invariant (the level-2 base of
`level_hashlifeResult_of_level_two`). The well-formedness is unconditional
too: four equal-level (level-0) leaves form a wf node, and `emptyOfLevel 1` is
wf (a node of four level-0 empty leaves). -/

private theorem level_step4x4 (c : MacroCell) : (step4x4 c).level = 1 := by
  by_cases h : c.level == 2
  · simp only [step4x4, if_pos h, MacroCell.level]
  · simp only [step4x4, if_neg h, emptyOfLevel_level]

private theorem wf_step4x4 (c : MacroCell) : (step4x4 c).wf = true := by
  by_cases h : c.level == 2
  · -- level-2 arm: node (leaf _) (leaf _) (leaf _) (leaf _). Four leaves are
    -- all wf (= true) and all level 0, so the wf conjunction is trivially true.
    simp only [step4x4, if_pos h, MacroCell.wf, MacroCell.level]
    decide
  · simp only [step4x4, if_neg h]
    exact emptyOfLevel_wf 1

/-! ## P4 structural input: level preservation (level-2 base)

`hashlifeResult` on a well-formed level-`k` cell is documented to return a
level-`(k-1)` cell (the centered `2^(k-1) × 2^(k-1)` region after `2^(k-2)`
generations). This level shape is a structural input to the P4
central-correctness assembly: both `result.toGrid (2^k, 2^k)` and the
`restrictGridTo` window presuppose the result is level-`(k+1)` (in the
level-`(k+2)` input's coordinates). The general statement
`(hashlifeResult c).level = c.level - 1` requires a strong-induction on the
double-nine recursion; the level-2 base case below is closed directly by
shape reduction to 16 leaves + definitional evaluation of `hashlifeResultAux`
(the `level == 2` arm yields `step4x4`, a `node` of four leaves → level 1). -/

/-- **Level-2 base of level-preservation**: a well-formed level-2
    `MacroCell` maps under `hashlifeResult` to a level-1 cell. -/
theorem level_hashlifeResult_of_level_two (c : MacroCell)
    (hwf : c.wf = true) (hk : c.level = 2) :
    (hashlifeResult c).level = 1 := by
  obtain ⟨a, b, d, e, rfl, ha⟩ := shape_of_level_succ c 1 hk
  obtain ⟨hwa, hwb, hwd, hwe, hlb, hld, hle⟩ := wf_node_elim hwf
  rw [ha] at hlb hld hle
  obtain ⟨a1, a2, a3, a4, rfl, ha1⟩ := shape_of_level_succ a 0 ha
  obtain ⟨b1, b2, b3, b4, rfl, hb1⟩ := shape_of_level_succ b 0 hlb
  obtain ⟨d1, d2, d3, d4, rfl, hd1⟩ := shape_of_level_succ d 0 hld
  obtain ⟨e1, e2, e3, e4, rfl, he1⟩ := shape_of_level_succ e 0 hle
  obtain ⟨_, _, _, _, hla2, hla3, hla4⟩ := wf_node_elim hwa
  obtain ⟨_, _, _, _, hlb2, hlb3, hlb4⟩ := wf_node_elim hwb
  obtain ⟨_, _, _, _, hld2, hld3, hld4⟩ := wf_node_elim hwd
  obtain ⟨_, _, _, _, hle2, hle3, hle4⟩ := wf_node_elim hwe
  rw [ha1] at hla2 hla3 hla4
  rw [hb1] at hlb2 hlb3 hlb4
  rw [hd1] at hld2 hld3 hld4
  rw [he1] at hle2 hle3 hle4
  obtain ⟨v1, rfl⟩ := shape_of_level_zero a1 ha1
  obtain ⟨v2, rfl⟩ := shape_of_level_zero a2 hla2
  obtain ⟨v3, rfl⟩ := shape_of_level_zero a3 hla3
  obtain ⟨v4, rfl⟩ := shape_of_level_zero a4 hla4
  obtain ⟨v5, rfl⟩ := shape_of_level_zero b1 hb1
  obtain ⟨v6, rfl⟩ := shape_of_level_zero b2 hlb2
  obtain ⟨v7, rfl⟩ := shape_of_level_zero b3 hlb3
  obtain ⟨v8, rfl⟩ := shape_of_level_zero b4 hlb4
  obtain ⟨v9, rfl⟩ := shape_of_level_zero d1 hd1
  obtain ⟨v10, rfl⟩ := shape_of_level_zero d2 hld2
  obtain ⟨v11, rfl⟩ := shape_of_level_zero d3 hld3
  obtain ⟨v12, rfl⟩ := shape_of_level_zero d4 hld4
  obtain ⟨v13, rfl⟩ := shape_of_level_zero e1 he1
  obtain ⟨v14, rfl⟩ := shape_of_level_zero e2 hle2
  obtain ⟨v15, rfl⟩ := shape_of_level_zero e3 hle3
  obtain ⟨v16, rfl⟩ := shape_of_level_zero e4 hle4
  -- c is now a concrete level-2 node of 16 leaves; `hashlifeResult` =
  -- `hashlifeResultAux 2 c`, the `level == 2` arm yields `step4x4 c` =
  -- `node (leaf _) (leaf _) (leaf _) (leaf _)` of level 1, by computation.
  rfl

/-- **Level-2 base of well-formedness preservation**: a well-formed level-2
    `MacroCell` maps under `hashlifeResult` to a well-formed cell. This is the
    wf sibling of `level_hashlifeResult_of_level_two`: the same 16-leaf shape
    reduction lands on `step4x4 c` (a `node` of four level-0 leaves), whose
    `.wf = true` is unconditional (`wf_step4x4`). P4 structural input: the
    wave-1 results `r_i` of the double-nine recursion must be wf so that the
    wave-2 `hashlifeResultAux` recursion does not hit its defensive
    `deadLeaf` arm (Hashlife.lean fuel-exhausted fallback). -/
theorem wf_hashlifeResult_of_level_two (c : MacroCell)
    (hwf : c.wf = true) (hk : c.level = 2) :
    (hashlifeResult c).wf = true := by
  obtain ⟨a, b, d, e, rfl, ha⟩ := shape_of_level_succ c 1 hk
  obtain ⟨hwa, hwb, hwd, hwe, hlb, hld, hle⟩ := wf_node_elim hwf
  rw [ha] at hlb hld hle
  obtain ⟨a1, a2, a3, a4, rfl, ha1⟩ := shape_of_level_succ a 0 ha
  obtain ⟨b1, b2, b3, b4, rfl, hb1⟩ := shape_of_level_succ b 0 hlb
  obtain ⟨d1, d2, d3, d4, rfl, hd1⟩ := shape_of_level_succ d 0 hld
  obtain ⟨e1, e2, e3, e4, rfl, he1⟩ := shape_of_level_succ e 0 hle
  obtain ⟨_, _, _, _, hla2, hla3, hla4⟩ := wf_node_elim hwa
  obtain ⟨_, _, _, _, hlb2, hlb3, hlb4⟩ := wf_node_elim hwb
  obtain ⟨_, _, _, _, hld2, hld3, hld4⟩ := wf_node_elim hwd
  obtain ⟨_, _, _, _, hle2, hle3, hle4⟩ := wf_node_elim hwe
  rw [ha1] at hla2 hla3 hla4
  rw [hb1] at hlb2 hlb3 hlb4
  rw [hd1] at hld2 hld3 hld4
  rw [he1] at hle2 hle3 hle4
  obtain ⟨v1, rfl⟩ := shape_of_level_zero a1 ha1
  obtain ⟨v2, rfl⟩ := shape_of_level_zero a2 hla2
  obtain ⟨v3, rfl⟩ := shape_of_level_zero a3 hla3
  obtain ⟨v4, rfl⟩ := shape_of_level_zero a4 hla4
  obtain ⟨v5, rfl⟩ := shape_of_level_zero b1 hb1
  obtain ⟨v6, rfl⟩ := shape_of_level_zero b2 hlb2
  obtain ⟨v7, rfl⟩ := shape_of_level_zero b3 hlb3
  obtain ⟨v8, rfl⟩ := shape_of_level_zero b4 hlb4
  obtain ⟨v9, rfl⟩ := shape_of_level_zero d1 hd1
  obtain ⟨v10, rfl⟩ := shape_of_level_zero d2 hld2
  obtain ⟨v11, rfl⟩ := shape_of_level_zero d3 hld3
  obtain ⟨v12, rfl⟩ := shape_of_level_zero d4 hld4
  obtain ⟨v13, rfl⟩ := shape_of_level_zero e1 he1
  obtain ⟨v14, rfl⟩ := shape_of_level_zero e2 hle2
  obtain ⟨v15, rfl⟩ := shape_of_level_zero e3 hle3
  obtain ⟨v16, rfl⟩ := shape_of_level_zero e4 hle4
  -- c is now a concrete level-2 node of 16 leaves; `hashlifeResult` =
  -- `hashlifeResultAux 2 c`, the `level == 2` arm yields `step4x4 c` =
  -- `node (leaf _) (leaf _) (leaf _) (leaf _)` of four wf level-0 leaves,
  -- whose `.wf` is `true` by reduction: wf inspects only levels (each leaf
  -- is level 0) and leaf-wf (each `true`), value-independent like the level
  -- sibling above (no GoL evaluation needed). Closes by `rfl`, mirroring
  -- `level_hashlifeResult_of_level_two`.
  rfl

/-- Exhaustive check of the P4 base case over the 16 leaf booleans of a
    (fully explicit) level-2 cell: `2^16` instances by `native_decide`. -/
private theorem p4_base_exhaustive :
    ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : Bool,
      (hashlifeResultAux 2
          (node (node (leaf v1) (leaf v2) (leaf v3) (leaf v4))
                (node (leaf v5) (leaf v6) (leaf v7) (leaf v8))
                (node (leaf v9) (leaf v10) (leaf v11) (leaf v12))
                (node (leaf v13) (leaf v14) (leaf v15) (leaf v16)))).toGrid
        ((1 : Int), (1 : Int))
      = restrictGridTo
          (evolve 1
            ((node (node (leaf v1) (leaf v2) (leaf v3) (leaf v4))
                   (node (leaf v5) (leaf v6) (leaf v7) (leaf v8))
                   (node (leaf v9) (leaf v10) (leaf v11) (leaf v12))
                   (node (leaf v13) (leaf v14) (leaf v15) (leaf v16))).toGrid
              (0, 0)))
          1 2 := by
  native_decide

/-- **P4 base case (k = 0), in general**: the corrected statement holds
    for every well-formed level-2 cell. -/
theorem hashlifeResult_central_correct_base (c : MacroCell)
    (hwf : c.wf = true) (hk : c.level = 2) :
    (hashlifeResultAux 2 c).toGrid ((1 : Int), (1 : Int))
    = restrictGridTo (evolve 1 (c.toGrid (0, 0))) 1 2 := by
  obtain ⟨a, b, d, e, rfl, ha⟩ := shape_of_level_succ c 1 hk
  obtain ⟨hwa, hwb, hwd, hwe, hlb, hld, hle⟩ := wf_node_elim hwf
  rw [ha] at hlb hld hle
  obtain ⟨a1, a2, a3, a4, rfl, ha1⟩ := shape_of_level_succ a 0 ha
  obtain ⟨b1, b2, b3, b4, rfl, hb1⟩ := shape_of_level_succ b 0 hlb
  obtain ⟨d1, d2, d3, d4, rfl, hd1⟩ := shape_of_level_succ d 0 hld
  obtain ⟨e1, e2, e3, e4, rfl, he1⟩ := shape_of_level_succ e 0 hle
  obtain ⟨_, _, _, _, hla2, hla3, hla4⟩ := wf_node_elim hwa
  obtain ⟨_, _, _, _, hlb2, hlb3, hlb4⟩ := wf_node_elim hwb
  obtain ⟨_, _, _, _, hld2, hld3, hld4⟩ := wf_node_elim hwd
  obtain ⟨_, _, _, _, hle2, hle3, hle4⟩ := wf_node_elim hwe
  rw [ha1] at hla2 hla3 hla4
  rw [hb1] at hlb2 hlb3 hlb4
  rw [hd1] at hld2 hld3 hld4
  rw [he1] at hle2 hle3 hle4
  obtain ⟨v1, rfl⟩ := shape_of_level_zero a1 ha1
  obtain ⟨v2, rfl⟩ := shape_of_level_zero a2 hla2
  obtain ⟨v3, rfl⟩ := shape_of_level_zero a3 hla3
  obtain ⟨v4, rfl⟩ := shape_of_level_zero a4 hla4
  obtain ⟨v5, rfl⟩ := shape_of_level_zero b1 hb1
  obtain ⟨v6, rfl⟩ := shape_of_level_zero b2 hlb2
  obtain ⟨v7, rfl⟩ := shape_of_level_zero b3 hlb3
  obtain ⟨v8, rfl⟩ := shape_of_level_zero b4 hlb4
  obtain ⟨v9, rfl⟩ := shape_of_level_zero d1 hd1
  obtain ⟨v10, rfl⟩ := shape_of_level_zero d2 hld2
  obtain ⟨v11, rfl⟩ := shape_of_level_zero d3 hld3
  obtain ⟨v12, rfl⟩ := shape_of_level_zero d4 hld4
  obtain ⟨v13, rfl⟩ := shape_of_level_zero e1 he1
  obtain ⟨v14, rfl⟩ := shape_of_level_zero e2 hle2
  obtain ⟨v15, rfl⟩ := shape_of_level_zero e3 hle3
  obtain ⟨v16, rfl⟩ := shape_of_level_zero e4 hle4
  exact p4_base_exhaustive v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
    v15 v16

/-! ## P4 inductive step — scaffolding for the double-nine decomposition

The sorry at `p4_ext_bridge c (k+1) (fun p => by sorry)` is the **research-level
verrou** of the whole module. It demands the pointwise membership biconditional:

    ∀ p, p ∈ (hashlifeResultAux (k+2) c).toGrid (2^k, 2^k)
         ↔ p ∈ restrictGridTo (evolve (2^k) (c.toGrid (0,0))) (2^k) (2^(k+1))

`p4_ext_bridge` (proven) reduces list-equality to this biconditional, so once
the biconditional is discharged, `hashlifeResult_central_correct` closes by
induction. The function `p4_succ_membership` below is the **single named
entry point** that gathers the four sub-lemmas; each sub-lemma is an
independent, difficulty-ranked prover target (grignotable one-per-session).

### Proof plan (the double-nine, two half-steps)

`hashlifeResultAux (k+3) c` on a well-formed level-`(k+2)` cell `c` unfolds
(via the structural-recursion pattern at `Hashlife.lean`) to:

  **Wave 1** — nine overlapping level-`(k+1)` sub-cells `n1..n9`, each recursed
  to a level-`k` result `r1..r9` that is `2^(k-1)` generations ahead (by IH).
  **Wave 2** — four overlapping level-`(k+1)` super-cells `q_nw..q_se` (built
  from the `r_i`), each recursed to a level-`k` result `out_*` that is another
  `2^(k-1)` generations ahead. The two half-steps compose to `2^k` generations,
  matching `evolve (2^k)` — this is the light-cone argument (P2) applied twice.

### Sub-lemmas (difficulty-ranked, each `grignotable` independently)

| Lemma | Difficulty | What it proves |
|-------|-----------|----------------|
| `p4_double_nine_shape`     | P4.1 (structural) | The 9 sub-cells `n_i` tile `c` and each has level `k+1` + is wf |
| `p4_wave1_ih`              | P4.2 (IH application) | Each `r_i = hashlifeResultAux (k+1) n_i` matches `evolve 2^(k-1)` on the `n_i` window (by IH at level `k`) |
| `p4_wave2_ih`              | P4.3 (IH application) | Each `out_* = hashlifeResultAux (k+1) q_*` matches `evolve 2^(k-1)` on the `q_*` window (by IH at level `k`) |
| `p4_half_steps_compose`    | P4.4 (compositional, hardest) | Wave1 ∘ Wave2 = `2^k` generations via `step_light_cone` (P2, proven) — the boundary of each sub-cell does not leak because the live region stays inside the centered window |

Once all four are proven, `p4_succ_membership` glues them. The ordering
P4.1 → P4.2 → P4.3 → P4.4 reflects dependency: P4.2/P4.3 need P4.1's shape
facts, P4.4 needs P4.2/P4.3. Each is **self-contained**: a session can
eliminate one without re-deriving the others.

See `agent_tests/prover/RUNBOOK.md` for the iteration protocol. -/

/-- **P4.1** (structural half, PROVEN): a well-formed level-`(k+2)` MacroCell
    decomposes into sixteen depth-2 grandchildren `nw_nw..se_se`, each of level
    `k` and well-formed. This is exactly the shape precondition
    `hashlifeResultAux`'s double-nine pattern match relies on: the nine sub-cells
    `n1..n9` of `Hashlife.lean` are each `node`s of four such grandchildren, so
    combined with `node_wf_level_of_four` this discharges every `n_i`'s
    `level = k + 1 ∧ wf = true`.

    The signature `(c : MacroCell)` is preserved so the `p4_succ_membership`
    glue (L1490) typechecks unchanged; the conclusion is the depth-2 existential
    decomposition plus the sixteen `level = k ∧ wf = true` facts, which is
    precisely `wf_node_depth2_grandchildren`'s output. The **geometric half**
    of P4.1 — that the `n_i` union tiles `c`'s live region (a statement on
    `toGrid`/`restrictGridTo` overlap, not just shape) — is genuinely
    non-structural and stays open (research-level, queueable behind the
    `step_light_cone` P2 machinery). -/
theorem p4_double_nine_shape
    (c : MacroCell) (k : Nat) (hwf : c.wf = true) (hk : c.level = k + 2) :
    ∃ nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
       sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell,
      c = node (node nw_nw nw_ne nw_sw nw_se)
               (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se)
               (node se_nw se_ne se_sw se_se) ∧
      nw_nw.level = k ∧ nw_nw.wf = true ∧
      nw_ne.level = k ∧ nw_ne.wf = true ∧
      nw_sw.level = k ∧ nw_sw.wf = true ∧
      nw_se.level = k ∧ nw_se.wf = true ∧
      ne_nw.level = k ∧ ne_nw.wf = true ∧
      ne_ne.level = k ∧ ne_ne.wf = true ∧
      ne_sw.level = k ∧ ne_sw.wf = true ∧
      ne_se.level = k ∧ ne_se.wf = true ∧
      sw_nw.level = k ∧ sw_nw.wf = true ∧
      sw_ne.level = k ∧ sw_ne.wf = true ∧
      sw_sw.level = k ∧ sw_sw.wf = true ∧
      sw_se.level = k ∧ sw_se.wf = true ∧
      se_nw.level = k ∧ se_nw.wf = true ∧
      se_ne.level = k ∧ se_ne.wf = true ∧
      se_sw.level = k ∧ se_sw.wf = true ∧
      se_se.level = k ∧ se_se.wf = true := by
  -- depth-1: c = node nw ne sw se with nw.level = k + 1
  obtain ⟨nw, ne, sw, se, rfl, hnw_lvl⟩ := shape_of_level_succ c (k + 1) hk
  obtain ⟨hnw, hne, hsw, hse, hne_eq, hsw_eq, hse_eq⟩ := wf_node_elim hwf
  -- siblings share nw's level
  have hne_lvl : ne.level = k + 1 := hne_eq ▸ hnw_lvl
  have hsw_lvl : sw.level = k + 1 := hsw_eq ▸ hnw_lvl
  have hse_lvl : se.level = k + 1 := hse_eq ▸ hnw_lvl
  -- depth-2: each quadrant is a node of four grandchildren
  obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, rfl, _⟩ := shape_of_level_succ nw k hnw_lvl
  obtain ⟨ne_nw, ne_ne, ne_sw, ne_se, rfl, _⟩ := shape_of_level_succ ne k hne_lvl
  obtain ⟨sw_nw, sw_ne, sw_sw, sw_se, rfl, _⟩ := shape_of_level_succ sw k hsw_lvl
  obtain ⟨se_nw, se_ne, se_sw, se_se, rfl, _⟩ := shape_of_level_succ se k hse_lvl
  refine ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, ?_⟩
  exact wf_node_depth2_grandchildren
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se k hk hwf

/-- Clean-context level helper (c.142). Computes the level of the double-nine
    outer node from its 16 grandchildren (level `n-2`) as a single arithmetic
    fact, so the pos arm of the preservation step helper does not whnf
    `(node …).level`'s type in the 32-fact context. -/
private theorem node16_level (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell) (n : Nat)
    (hn2 : 2 ≤ n) (h : nw_nw.level = n - 2) :
    (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
          (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).level = n := by
  show 1 + (1 + nw_nw.level) = n
  omega

/-- **P4.4 assembly grain (c.156).** In a CLEAN context (the 16 grandchildren as
    opaque binders + one level hypothesis), the `hashlifeResultAux_succ_node`
    if-condition `(node16).level == 2` is false for `k ≥ 1` (the node level is
    `k + 2 ≥ 3`). Proven standalone because stating/rewriting `(node16).level`
    INLINE inside `p4_succ_membership`'s rich context (post `_h1`/`_h2`/`_h3`/`_h4`
    obtain of 16 gc's) whnf-diverges (the c.142 pathology). Applying this helper
    there keeps the level term inferred, never re-elaborated — the opaque-binder
    pattern of c.139/c.143. -/
private theorem node16_level_ne_two (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hnw : nw_nw.level = k) :
    ¬ ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
             (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).level == 2) := by
  -- Mirror the working pos-arm discharge at L1810-1815: `beq_iff_eq` converts the
  -- `==` (Nat.beq) to `=`, then omega finds k+2 = 2 contradicts k >= 1.
  intro heq
  have hnode := node16_level nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
               sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se (k + 2) (by omega) (by omega)
  rw [hnode] at heq
  have hn2 : k + 2 = 2 := by simpa [beq_iff_eq] using heq
  omega

/-- Apply the level/`cellWf` IH to a `node` of four level-`(n-2)` `cellWf` cells
    (c.142 workhorse), for BOTH wave layers of the preservation lemma: wave-1
    (the nine `n_i`, each a `node` of four grandchildren) and wave-2 (the four
    `q_*`, each a `node` of four wave-1 results `r_i`). Clean context (four
    cells as opaque binders) avoids the whnf divergence an inline `ih`
    application hits in the step helper's rich context (c.139 pattern). -/
private theorem cellWf_quad (n : Nat) (hn3 : 3 ≤ n)
    (ih : ∀ (m : Nat), m < n → ∀ (c' : MacroCell), cellWf c' → c'.level = m → 2 ≤ m →
            ((hashlifeResultAux m c').level = m - 1 ∧ cellWf (hashlifeResultAux m c')))
    (g1 g2 g3 g4 : MacroCell)
    (hg1 : g1.level = n - 2) (hg2 : g2.level = n - 2)
    (hg3 : g3.level = n - 2) (hg4 : g4.level = n - 2)
    (hw1 : cellWf g1) (hw2 : cellWf g2) (hw3 : cellWf g3) (hw4 : cellWf g4) :
    ((hashlifeResultAux (n - 1) (node g1 g2 g3 g4)).level = n - 2 ∧
     cellWf (hashlifeResultAux (n - 1) (node g1 g2 g3 g4))) := by
  have hqwf : cellWf (node g1 g2 g3 g4) :=
    cellWf.node hw1 hw2 hw3 hw4 (by omega) (by omega) (by omega)
  have hqlvl : (node g1 g2 g3 g4).level = n - 1 := by show 1 + g1.level = n - 1; omega
  exact ih (n - 1) (by omega) (node g1 g2 g3 g4) hqwf hqlvl (by omega)

/-- Clean-context conjunct-closer (c.142, c.139 pattern). Closes the level AND
    `cellWf` conjuncts of a `node` of four wave-2 results `out_*`, with the four
    cells as OPAQUE binders. Inside, `out_nw.level` etc. are atoms to `omega`
    (no whnf), so the level conjunct closes; `cellWf.node` constructor closes the
    `cellWf` conjunct syntactically. This isolation is required because closing
    these conjuncts INLINE in the step helper (where `out_*` are spelled-out
    `hashlifeResultAux` terms) makes `omega`/`rw` `whnf`-normalize
    `(hashlifeResultAux (n-1) q_*)`.level` recursively → divergent (c.142 Exp1-3). -/
private theorem node_level_cellWf_conjuncts (n : Nat) (hn3 : 3 ≤ n)
    (out_nw out_ne out_sw out_se : MacroCell)
    (hnw : out_nw.level = n - 2) (hne : out_ne.level = n - 2)
    (hsw : out_sw.level = n - 2) (hse : out_se.level = n - 2)
    (hw_nw : cellWf out_nw) (hw_ne : cellWf out_ne)
    (hw_sw : cellWf out_sw) (hw_se : cellWf out_se) :
    (node out_nw out_ne out_sw out_se).level = n - 1 ∧
    cellWf (node out_nw out_ne out_sw out_se) := by
  refine ⟨?_, ?_⟩
  · show 1 + out_nw.level = n - 1; omega
  · exact cellWf.node hw_nw hw_ne hw_sw hw_se (by omega) (by omega) (by omega)

/-- Step helper for `hashlifeResultAux_level_cellWf` (c.142). Unfolds the
    double-nine recursive arm of `hashlifeResultAux` in the clean-probe context,
    builds the wave-1 results `r_i` and wave-2 results `out_*` via `cellWf_quad`,
    and closes both conjuncts. The `cellWf` conclusion (opaque to defeq) is what
    makes the wf conjunct closeable — the transparent `.wf` version diverges on
    whnf for the nested `hashlifeResultAux` results (c.140, 8M heartbeats). -/
private theorem hashlifeResultAux_level_cellWf_step (n : Nat) (hn3 : 3 ≤ n)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hgrands : nw_nw.level = n - 2 ∧ nw_nw.wf = true ∧
               nw_ne.level = n - 2 ∧ nw_ne.wf = true ∧
               nw_sw.level = n - 2 ∧ nw_sw.wf = true ∧
               nw_se.level = n - 2 ∧ nw_se.wf = true ∧
               ne_nw.level = n - 2 ∧ ne_nw.wf = true ∧
               ne_ne.level = n - 2 ∧ ne_ne.wf = true ∧
               ne_sw.level = n - 2 ∧ ne_sw.wf = true ∧
               ne_se.level = n - 2 ∧ ne_se.wf = true ∧
               sw_nw.level = n - 2 ∧ sw_nw.wf = true ∧
               sw_ne.level = n - 2 ∧ sw_ne.wf = true ∧
               sw_sw.level = n - 2 ∧ sw_sw.wf = true ∧
               sw_se.level = n - 2 ∧ sw_se.wf = true ∧
               se_nw.level = n - 2 ∧ se_nw.wf = true ∧
               se_ne.level = n - 2 ∧ se_ne.wf = true ∧
               se_sw.level = n - 2 ∧ se_sw.wf = true ∧
               se_se.level = n - 2 ∧ se_se.wf = true)
    (ih : ∀ (m : Nat), m < n → ∀ (c' : MacroCell), cellWf c' → c'.level = m → 2 ≤ m →
            ((hashlifeResultAux m c').level = m - 1 ∧ cellWf (hashlifeResultAux m c'))) :
    ((hashlifeResultAux n
        (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
              (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se))).level = n - 1 ∧
     cellWf (hashlifeResultAux n
        (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
              (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)))) := by
  obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
          hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
          hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
          hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hgrands
  rw [show n = (n - 1) + 1 from by omega]
  by_cases heq : (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
                     (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).level == 2
  · -- pos arm: node level == 2, but 16 grandchildren level (n-2) give node level n ≥ 3.
    have hnode := node16_level nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
                 sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se n (by omega) hnw_nw_l
    rw [hnode] at heq
    have hn2 : n = 2 := by simpa [beq_iff_eq] using heq
    exfalso; omega
  · -- neg arm: the recursive double-nine body.
    simp only [MacroCell.level] at heq
    have hr1 := cellWf_quad n hn3 ih nw_nw nw_ne nw_sw nw_se
                   hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                   (cellWf_of_wf _ hnw_nw_w) (cellWf_of_wf _ hnw_ne_w)
                   (cellWf_of_wf _ hnw_sw_w) (cellWf_of_wf _ hnw_se_w)
    have hr2 := cellWf_quad n hn3 ih nw_ne ne_nw nw_se ne_sw
                   hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                   (cellWf_of_wf _ hnw_ne_w) (cellWf_of_wf _ hne_nw_w)
                   (cellWf_of_wf _ hnw_se_w) (cellWf_of_wf _ hne_sw_w)
    have hr3 := cellWf_quad n hn3 ih ne_nw ne_ne ne_sw ne_se
                   hne_nw_l hne_ne_l hne_sw_l hne_se_l
                   (cellWf_of_wf _ hne_nw_w) (cellWf_of_wf _ hne_ne_w)
                   (cellWf_of_wf _ hne_sw_w) (cellWf_of_wf _ hne_se_w)
    have hr4 := cellWf_quad n hn3 ih nw_sw nw_se sw_nw sw_ne
                   hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                   (cellWf_of_wf _ hnw_sw_w) (cellWf_of_wf _ hnw_se_w)
                   (cellWf_of_wf _ hsw_nw_w) (cellWf_of_wf _ hsw_ne_w)
    have hr5 := cellWf_quad n hn3 ih nw_se ne_sw sw_ne se_nw
                   hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                   (cellWf_of_wf _ hnw_se_w) (cellWf_of_wf _ hne_sw_w)
                   (cellWf_of_wf _ hsw_ne_w) (cellWf_of_wf _ hse_nw_w)
    have hr6 := cellWf_quad n hn3 ih ne_sw ne_se se_nw se_ne
                   hne_sw_l hne_se_l hse_nw_l hse_ne_l
                   (cellWf_of_wf _ hne_sw_w) (cellWf_of_wf _ hne_se_w)
                   (cellWf_of_wf _ hse_nw_w) (cellWf_of_wf _ hse_ne_w)
    have hr7 := cellWf_quad n hn3 ih sw_nw sw_ne sw_sw sw_se
                   hsw_nw_l hsw_ne_l hsw_sw_l hsw_se_l
                   (cellWf_of_wf _ hsw_nw_w) (cellWf_of_wf _ hsw_ne_w)
                   (cellWf_of_wf _ hsw_sw_w) (cellWf_of_wf _ hsw_se_w)
    have hr8 := cellWf_quad n hn3 ih sw_ne se_nw sw_se se_sw
                   hsw_ne_l hse_nw_l hsw_se_l hse_sw_l
                   (cellWf_of_wf _ hsw_ne_w) (cellWf_of_wf _ hse_nw_w)
                   (cellWf_of_wf _ hsw_se_w) (cellWf_of_wf _ hse_sw_w)
    have hr9 := cellWf_quad n hn3 ih se_nw se_ne se_sw se_se
                   hse_nw_l hse_ne_l hse_sw_l hse_se_l
                   (cellWf_of_wf _ hse_nw_w) (cellWf_of_wf _ hse_ne_w)
                   (cellWf_of_wf _ hse_sw_w) (cellWf_of_wf _ hse_se_w)
    -- Wave 2: q_* = node of four r_i; out_* = hRA (n-1) q_*.
    have honw := cellWf_quad n hn3 ih (hashlifeResultAux (n - 1) (node nw_nw nw_ne nw_sw nw_se))
                           (hashlifeResultAux (n - 1) (node nw_ne ne_nw nw_se ne_sw))
                           (hashlifeResultAux (n - 1) (node nw_sw nw_se sw_nw sw_ne))
                           (hashlifeResultAux (n - 1) (node nw_se ne_sw sw_ne se_nw))
                           hr1.1 hr2.1 hr4.1 hr5.1 hr1.2 hr2.2 hr4.2 hr5.2
    have hone := cellWf_quad n hn3 ih (hashlifeResultAux (n - 1) (node nw_ne ne_nw nw_se ne_sw))
                           (hashlifeResultAux (n - 1) (node ne_nw ne_ne ne_sw ne_se))
                           (hashlifeResultAux (n - 1) (node nw_se ne_sw sw_ne se_nw))
                           (hashlifeResultAux (n - 1) (node ne_sw ne_se se_nw se_ne))
                           hr2.1 hr3.1 hr5.1 hr6.1 hr2.2 hr3.2 hr5.2 hr6.2
    have hosw := cellWf_quad n hn3 ih (hashlifeResultAux (n - 1) (node nw_sw nw_se sw_nw sw_ne))
                           (hashlifeResultAux (n - 1) (node nw_se ne_sw sw_ne se_nw))
                           (hashlifeResultAux (n - 1) (node sw_nw sw_ne sw_sw sw_se))
                           (hashlifeResultAux (n - 1) (node sw_ne se_nw sw_se se_sw))
                           hr4.1 hr5.1 hr7.1 hr8.1 hr4.2 hr5.2 hr7.2 hr8.2
    have hose := cellWf_quad n hn3 ih (hashlifeResultAux (n - 1) (node nw_se ne_sw sw_ne se_nw))
                           (hashlifeResultAux (n - 1) (node ne_sw ne_se se_nw se_ne))
                           (hashlifeResultAux (n - 1) (node sw_ne se_nw sw_se se_sw))
                           (hashlifeResultAux (n - 1) (node se_nw se_ne se_sw se_se))
                           hr5.1 hr6.1 hr8.1 hr9.1 hr5.2 hr6.2 hr8.2 hr9.2
    -- Unfold hRA's recursive arm now that the wave facts are established.
    simp only [hashlifeResultAux, if_neg heq, MacroCell.level]
    exact node_level_cellWf_conjuncts n hn3 _ _ _ _
        honw.1 hone.1 hosw.1 hose.1 honw.2 hone.2 hosw.2 hose.2

/-- **(c.142) Level + well-formedness preservation of `hashlifeResultAux`**,
    over the OPAQUE `cellWf` predicate. For `2 ≤ L` and a well-formed level-`L`
    cell, `hashlifeResultAux L c` is well-formed and level `L - 1`.

    This is the gate for P4.3 (and the wave-2 layer of the lane): wave-2
    super-cells `q_*` are built from `hashlifeResultAux` RESULTS `r_i`, so
    instantiating the central-correctness IH on `q_*` requires `r_i`'s level
    and well-formedness — which only this lemma provides. c.140 proved the
    transparent `.wf` version diverges on whnf (8M heartbeats); the opaque
    `cellWf` conclusion breaks that defeq divergence. -/
theorem hashlifeResultAux_level_cellWf :
    ∀ (L : Nat) (c : MacroCell), cellWf c → c.level = L → 2 ≤ L →
      ((hashlifeResultAux L c).level = L - 1 ∧ cellWf (hashlifeResultAux L c)) := by
  intro L
  induction L using Nat.strongRecOn with
  | ind n ih =>
    intro c hwf hc hn2
    by_cases h2 : n = 2
    · subst h2
      refine ⟨?_, ?_⟩
      · have hdef : hashlifeResultAux 2 c = hashlifeResult c := by
          show hashlifeResultAux 2 c = hashlifeResultAux c.level c
          rw [hc]
        rw [hdef]
        exact level_hashlifeResult_of_level_two c (wf_of_cellWf hwf) hc
      · have hdef : hashlifeResultAux 2 c = hashlifeResult c := by
          show hashlifeResultAux 2 c = hashlifeResultAux c.level c
          rw [hc]
        rw [hdef]
        exact cellWf_of_wf _ (wf_hashlifeResult_of_level_two c (wf_of_cellWf hwf) hc)
    · have hn3 : 3 ≤ n := by omega
      have hk' : c.level = (n - 2) + 2 := by omega
      obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
              sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, hgrands⟩ :=
        p4_double_nine_shape c (n - 2) (wf_of_cellWf hwf) hk'
      exact hashlifeResultAux_level_cellWf_step n hn3
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hgrands ih

/-- The central-correctness statement, abstracted as a named predicate.
    Quoting it as `centralCorrect c j` (instead of the unfolded `2^j`-indexed
    Grid equality) stops the elaborator from running `whnf` on
    `hashlifeResultAux (j+2) c.toGrid` while checking the `ih` argument type of
    `p4_wave1_ih`; that reduction diverges (it pattern-matches `c`, a free
    variable). Unlike the c.138 `@[irreducible]` variant, a plain `def` still
    allows defeq at the `hashlifeResult_central_correct` -> `p4_succ_membership`
    threading boundary (c.139). -/
def centralCorrect (c : MacroCell) (j : Nat) : Prop :=
  (hashlifeResultAux (j + 2) c).toGrid ((2^j : Nat), (2^j : Nat)) =
    restrictGridTo (evolve (2^j) (c.toGrid (0, 0))) (2^j : Int) (2^(j+1))

/-- **The whnf-wall bypass (4th abstraction technique, c.153).**

    `centralCorrect c j` is a *grid equality*. To reason about pointwise
    membership `p ∈ (hashlifeResultAux (j+2) c).toGrid off` WITHOUT whnf-reducing
    the `hashlifeResultAux` term (the wall that blocked c.138–c.140), apply
    `p ∈ ·` to both sides of the equality by **congruence** (`congrArg`), then
    `Iff.of_eq`. This substitutes the `hashlifeResultAux` term *syntactically* —
    it is never unfolded. The four previous techniques (opaque-binder helper
    c.139, `inductive cellWf` c.142, plain `def centralCorrect` c.139,
    `set m := k-1` c.147) all work *around* the wall by hiding hRA behind an
    opaque binder; this one crosses it by congruence, which is exactly what
    G2/G3 need (they must inspect the *membership* of the composed result, not
    just its level/wf).

    Instantiated with `mem_restrictGridTo`, this is the **G1 reduction**
    (membership of a sub-cell whose `centralCorrect` is known, e.g. `q_j` via
    `ih`) in one sorry-free step. The residual wall is **G3 assembly** (how
    `(hashlifeResultAux (k+2) c).toGrid off` decomposes into the four
    `(hashlifeResultAux (k+1) q_j).toGrid off_j` — the `toCellsAux` walk on an
    `hRA` that unfolds), which remains to be bridged. This lemma is the
    `p4_succ_membership` analogue of the P4.3 gate lemma (`hashlifeResultAux_
    level_cellWf`, c.142): sorry-stable infrastructure that unlocks the next
    attack. -/
theorem centralCorrect_mem (c : MacroCell) (j : Nat) (p : Int × Int)
    (h : centralCorrect c j) :
    p ∈ (hashlifeResultAux (j + 2) c).toGrid ((2^j : Nat), (2^j : Nat)) ↔
      isAlive (evolve (2^j) (c.toGrid (0, 0))) p = true ∧
      (2^j : Int) ≤ p.1 ∧ p.1 < (2^j : Int) + 2^(j+1) ∧
      (2^j : Int) ≤ p.2 ∧ p.2 < (2^j : Int) + 2^(j+1) := by
  have hb : p ∈ (hashlifeResultAux (j + 2) c).toGrid ((2^j : Nat), (2^j : Nat)) ↔
      p ∈ restrictGridTo (evolve (2^j) (c.toGrid (0, 0))) (2^j : Int) (2^(j+1)) :=
    Iff.of_eq (congrArg (fun g : Grid => p ∈ g) h)
  rw [hb, mem_restrictGridTo]
  refine ⟨fun ⟨Hm, h1, h2, h3, h4⟩ => ⟨?_, h1, h2, h3, h4⟩,
          fun ⟨H, h1, h2, h3, h4⟩ => ⟨?_, h1, h2, h3, h4⟩⟩ <;>
    simp_all [isAlive]

/-- **Offset-generalized centralCorrect membership** (P4.4 offset-matching G2 gate).

    `centralCorrect_mem` characterizes membership of a cell's result at its
    *canonical* centered offset `(2^j, 2^j)`. The P4.4 offset-matching assembly
    needs the same characterization at the **quadrant offsets** where the
    super-cells `q_*` actually sit in the parent result node (e.g. NW quadrant at
    `(2^k, 2^k)`, per `mem_toGrid_node`). This lemma re-anchors
    `centralCorrect_mem` from `(2^j, 2^j)` to an arbitrary offset `(a, b)` via
    `toGrid_shift_between`: the alive-status is evaluated at the back-shifted
    point `(p.1 - a + 2^j, p.2 - b + 2^j)`, and the centered window bounds
    `[2^j, 2^j + 2^(j+1))` translate to `[a, a + 2^(j+1))` (and `[b, b + 2^(j+1))`).

    Pure composition of `centralCorrect_mem` (G2 congruence, c.153) and
    `toGrid_shift_between` (#4797, the double-shift ingredient) — sorry-free gate
    ingredient. The residual research heart (sorry 4→3) is `evolve_half_step`,
    which consumes this gate to connect the induction hypothesis
    `centralCorrect q_* (k-1)` to the four quadrant offsets at once. -/
theorem centralCorrect_mem_shift (c : MacroCell) (j : Nat) (a b : Int) (p : Int × Int)
    (h : centralCorrect c j) :
    p ∈ (hashlifeResultAux (j + 2) c).toGrid (a, b) ↔
      isAlive (evolve (2^j) (c.toGrid (0, 0)))
        (p.1 - a + (2^j : Int), p.2 - b + (2^j : Int)) = true ∧
      a ≤ p.1 ∧ p.1 < a + 2^(j+1) ∧
      b ≤ p.2 ∧ p.2 < b + 2^(j+1) := by
  -- Re-anchor `(a,b)` → the canonical `(2^j,2^j)` offset. `centralCorrect_mem`'s
  -- canonical offset is the Nat-cast `↑(2^j)` (the display of `(2^j : Nat)`
  -- coerced to Int), so we instantiate `toGrid_shift_between` with
  -- `a' = b' = (2^j : Nat)` to match its rewrite pattern (native `(2^j : Int)`
  -- would not unify — the c.146/c.147 native-Int-vs-Nat-cast distinction).
  have hshift : p ∈ (hashlifeResultAux (j + 2) c).toGrid (a, b) ↔
      (p.1 - a + (2^j : Nat), p.2 - b + (2^j : Nat)) ∈
        (hashlifeResultAux (j + 2) c).toGrid ((2^j : Nat), (2^j : Nat)) :=
    toGrid_shift_between
  rw [hshift, centralCorrect_mem c j _ h]
  -- `centralCorrect_mem`'s bounds carry native `(2^j : Int)` literals, while the
  -- substituted point carries `↑(2^j)` (Nat-cast). Normalize to a single atom
  -- (c.146: linarith otherwise sees `↑(2^j)` and `(2^j : Int)` as unrelated).
  rw [show ((2 : Nat)^j).cast = (2^j : Int) from Nat.cast_pow 2 j]
  refine ⟨fun ⟨H, h1, h2, h3, h4⟩ => ⟨H, ?_, ?_, ?_, ?_⟩,
          fun ⟨H, h1, h2, h3, h4⟩ => ⟨H, ?_, ?_, ?_, ?_⟩⟩ <;> linarith

/-- **P4.2 helper (c.139 workaround).** The `ih` *application*
    `ih (node nw_se ne_sw sw_ne se_nk) (k-1) ...` diverges on `whnf` when it
    appears inline inside `p4_wave1_ih`'s body, because there the four
    grandchildren are free variables tied into a 16-grandchild / 32-fact local
    context (post `p4_double_nine_shape` obtain). Moving the application into
    this standalone helper makes `nw_se` etc. opaque binders at the application
    site, which is enough to stop the divergence (minimal-repro probe
    `WhnfProbe.lean`, arm 4 diverges / arm 6 compiles). -/
private theorem p4_wave1_ih_step
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_se ne_sw sw_ne se_nw : MacroCell)
    (hnw_se_l : nw_se.level = k) (hne_sw_l : ne_sw.level = k)
    (hsw_ne_l : sw_ne.level = k) (hse_nw_l : se_nw.level = k)
    (hnw_se_w : nw_se.wf = true) (hne_sw_w : ne_sw.wf = true)
    (hsw_ne_w : sw_ne.wf = true) (hse_nw_w : se_nw.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j) :
    centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) := by
  have hn5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                    hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
  exact ih (node nw_se ne_sw sw_ne se_nw) (k - 1) (by omega) hn5.2 (by omega)

/-- **P4.3 helper (c.142/c.139 pattern).** Wave-1 result facts for one sub-cell
    `n` (a double-nine `n_i`): `n`'s level-`(k+1)` well-formedness yields, via the
    proven preservation lemma `hashlifeResultAux_level_cellWf`, that the wave-1
    result `hashlifeResultAux (k+1) n` has level `k` and `cellWf`. `n` is an
    OPAQUE binder here so the `hashlifeResultAux` term in the conclusion does not
    whnf-reduce (calling the preservation lemma inline, with `n` spelled out as a
    `node` of grandchildren, makes the elaborator whnf the conclusion's nested
    `hashlifeResultAux` term — divergent). -/
private theorem wave1_result_facts (k : Nat) (hk1 : 1 ≤ k) (n : MacroCell)
    (hn_wf : n.wf = true) (hn_lvl : n.level = k + 1) :
    (hashlifeResultAux (k + 1) n).level = k ∧ cellWf (hashlifeResultAux (k + 1) n) := by
  have hcn := cellWf_of_wf n hn_wf
  exact hashlifeResultAux_level_cellWf (k + 1) n hcn hn_lvl (by omega)

/-- **P4.3 helper (wave 2).** The `ih` *application*
    `ih (node r1 r2 r4 r5) (k - 1) ...` for the NW super-cell `q_nw`
    (`= node r1 r2 r4 r5`, the four wave-1 results `r_i`), done in a standalone
    helper so the four `r_i` are opaque binders at the application site —
    same whnf-isolation pattern as `p4_wave1_ih_step` (c.139). The `r_i` are
    `hashlifeResultAux` results whose level (`k`) and `cellWf` are established
    by the proven preservation lemma `hashlifeResultAux_level_cellWf` (c.142),
    then bridged to `.wf = true` for the central-correctness `ih` (which is on
    `.wf`). `q_nw` is taken as representative (the three other super-cells are
    isomorphic, queued). -/
private theorem p4_wave2_ih_step
    (k : Nat) (hk1 : 1 ≤ k)
    (r1 r2 r4 r5 : MacroCell)
    (hr1_l : r1.level = k) (hr2_l : r2.level = k)
    (hr4_l : r4.level = k) (hr5_l : r5.level = k)
    (hr1_w : r1.wf = true) (hr2_w : r2.wf = true)
    (hr4_w : r4.wf = true) (hr5_w : r5.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j) :
    centralCorrect (node r1 r2 r4 r5) (k - 1) := by
  have hq := node_wf_level_of_four hr1_l hr2_l hr4_l hr5_l
                                    hr1_w hr2_w hr4_w hr5_w
  exact ih (node r1 r2 r4 r5) (k - 1) (by omega) hq.2 (by omega)

/-- **P4.2** (IH application, wave 1): for the center sub-cell
    `n5 = node nw_se ne_sw sw_ne se_nw` of the double-nine decomposition,
    `hashlifeResultAux (k+1) n5` agrees with `evolve (2^(k-1))` on `n5`'s
    centered window. This is the induction hypothesis (passed in explicitly by
    `p4_succ_membership`, breaking the cyclic back-reference to
    `hashlifeResult_central_correct`) applied to the level-`(k+1)` sub-cell
    `n5` (whose level is `k+1 = (k-1)+2`). The `ih` application is delegated to
    `p4_wave1_ih_step` (c.139 workaround for the whnf divergence). -/
theorem p4_wave1_ih
    (c : MacroCell) (k : Nat) (hwf : c.wf = true) (hk : c.level = k + 2) (hk1 : 1 ≤ k)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j) :
    ∃ nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
       sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell,
      c = node (node nw_nw nw_ne nw_sw nw_se)
               (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se)
               (node se_nw se_ne se_sw se_se) ∧
      centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) := by
  obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, hgrands⟩ :=
    p4_double_nine_shape c k hwf hk
  obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
          hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
          hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
          hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ :=
    hgrands
  refine ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, ?_⟩
  exact p4_wave1_ih_step k hk1 nw_se ne_sw sw_ne se_nw
          hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
          hnw_se_w hne_sw_w hsw_ne_w hse_nw_w ih


/-- **P4.3** (IH application, wave 2): for each of the four super-cells
    `q_*` built from the wave-1 results `r_i`, `hashlifeResultAux (k+1) q_*`
    agrees with `evolve (2^(k-1))` on `q_*`'s centered window. Same shape as
    P4.2 but on the second wave of the double-nine. Difficulty: P4.3
    (mechanical IH, structurally identical to P4.2 — may factor through a
    common helper). -/
theorem p4_wave2_ih
    (c : MacroCell) (k : Nat) (hwf : c.wf = true) (hk : c.level = k + 2) (hk1 : 1 ≤ k)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j) :
    ∃ nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
       sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell,
      c = node (node nw_nw nw_ne nw_sw nw_se)
               (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se)
               (node se_nw se_ne se_sw se_se) ∧
      centralCorrect
        (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
              (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
              (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
              (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
        (k - 1) ∧
      centralCorrect
        (node (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
              (hashlifeResultAux (k + 1) (node ne_nw ne_ne ne_sw ne_se))
              (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
              (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne)))
        (k - 1) ∧
      centralCorrect
        (node (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
              (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
              (hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
              (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw)))
        (k - 1) ∧
      centralCorrect
        (node (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
              (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
              (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
              (hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se)))
        (k - 1) := by
  obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, hgrands⟩ :=
    p4_double_nine_shape c k hwf hk
  obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
          hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
          hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
          hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ :=
    hgrands
  -- n1 = node nw_nw nw_ne nw_sw nw_se: level+wf, then preservation (c.142) -> r1 facts.
  have hq1 := node_wf_level_of_four hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                                    hnw_nw_w hnw_ne_w hnw_sw_w hnw_se_w
  have hr1 := wave1_result_facts k hk1 (node nw_nw nw_ne nw_sw nw_se) hq1.2 hq1.1
  -- n2 = node nw_ne ne_nw nw_se ne_sw
  have hq2 := node_wf_level_of_four hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                                    hnw_ne_w hne_nw_w hnw_se_w hne_sw_w
  have hr2 := wave1_result_facts k hk1 (node nw_ne ne_nw nw_se ne_sw) hq2.2 hq2.1
  -- n3 = node ne_nw ne_ne ne_sw ne_se
  have hq3 := node_wf_level_of_four hne_nw_l hne_ne_l hne_sw_l hne_se_l
                                    hne_nw_w hne_ne_w hne_sw_w hne_se_w
  have hr3 := wave1_result_facts k hk1 (node ne_nw ne_ne ne_sw ne_se) hq3.2 hq3.1
  -- n4 = node nw_sw nw_se sw_nw sw_ne
  have hq4 := node_wf_level_of_four hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                                    hnw_sw_w hnw_se_w hsw_nw_w hsw_ne_w
  have hr4 := wave1_result_facts k hk1 (node nw_sw nw_se sw_nw sw_ne) hq4.2 hq4.1
  -- n5 = node nw_se ne_sw sw_ne se_nw
  have hq5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                    hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
  have hr5 := wave1_result_facts k hk1 (node nw_se ne_sw sw_ne se_nw) hq5.2 hq5.1
  -- n6 = node ne_sw ne_se se_nw se_ne
  have hq6 := node_wf_level_of_four hne_sw_l hne_se_l hse_nw_l hse_ne_l
                                    hne_sw_w hne_se_w hse_nw_w hse_ne_w
  have hr6 := wave1_result_facts k hk1 (node ne_sw ne_se se_nw se_ne) hq6.2 hq6.1
  -- n7 = node sw_nw sw_ne sw_sw sw_se
  have hq7 := node_wf_level_of_four hsw_nw_l hsw_ne_l hsw_sw_l hsw_se_l
                                    hsw_nw_w hsw_ne_w hsw_sw_w hsw_se_w
  have hr7 := wave1_result_facts k hk1 (node sw_nw sw_ne sw_sw sw_se) hq7.2 hq7.1
  -- n8 = node sw_ne se_nw sw_se se_sw
  have hq8 := node_wf_level_of_four hsw_ne_l hse_nw_l hsw_se_l hse_sw_l
                                    hsw_ne_w hse_nw_w hsw_se_w hse_sw_w
  have hr8 := wave1_result_facts k hk1 (node sw_ne se_nw sw_se se_sw) hq8.2 hq8.1
  -- n9 = node se_nw se_ne se_sw se_se
  have hq9 := node_wf_level_of_four hse_nw_l hse_ne_l hse_sw_l hse_se_l
                                    hse_nw_w hse_ne_w hse_sw_w hse_se_w
  have hr9 := wave1_result_facts k hk1 (node se_nw se_ne se_sw se_se) hq9.2 hq9.1
  refine ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, ?_, ?_, ?_, ?_⟩
  · -- q_nw = node r1 r2 r4 r5
    exact p4_wave2_ih_step k hk1
            (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
            (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
            (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
            (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
            hr1.1 hr2.1 hr4.1 hr5.1
            (wf_of_cellWf hr1.2) (wf_of_cellWf hr2.2)
            (wf_of_cellWf hr4.2) (wf_of_cellWf hr5.2) ih
  · -- q_ne = node r2 r3 r5 r6
    exact p4_wave2_ih_step k hk1
            (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
            (hashlifeResultAux (k + 1) (node ne_nw ne_ne ne_sw ne_se))
            (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
            (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
            hr2.1 hr3.1 hr5.1 hr6.1
            (wf_of_cellWf hr2.2) (wf_of_cellWf hr3.2)
            (wf_of_cellWf hr5.2) (wf_of_cellWf hr6.2) ih
  · -- q_sw = node r4 r5 r7 r8
    exact p4_wave2_ih_step k hk1
            (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
            (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
            (hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
            (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
            hr4.1 hr5.1 hr7.1 hr8.1
            (wf_of_cellWf hr4.2) (wf_of_cellWf hr5.2)
            (wf_of_cellWf hr7.2) (wf_of_cellWf hr8.2) ih
  · -- q_se = node r5 r6 r8 r9
    exact p4_wave2_ih_step k hk1
            (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
            (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
            (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
            (hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se))
            hr5.1 hr6.1 hr8.1 hr9.1
            (wf_of_cellWf hr5.2) (wf_of_cellWf hr6.2)
            (wf_of_cellWf hr8.2) (wf_of_cellWf hr9.2) ih

/-! ### P4.4 decomposition — balisage en sous-sorries

The research-level composition `evolve (2^k) = evolve (2^(k-1)) ∘ evolve (2^(k-1))`
on the centered window is decomposed into four named sub-goals, each
independently attackable. This turns the monolithic P4.4 `sorry` into a chain
of milestones with clear interfaces (the same methodology that isolated
`hashlifeResultAux_level_cellWf` as a sub-goal unblocked P4.3, c.142).

- **S1 (CLOSED — `evolve_add` below)** : function-iteration composition.
  `evolve (a + b) g = evolve a (evolve b g)`. Pure `step^[·]` arithmetic, no
  `hashlifeResultAux`, no whnf wall — proven.
- **S2 (CLOSED — `window_cone_in_domain` below)** : boundary does not leak —
  for `p` in the centered window `[2^k, 2^k + 2^(k+1))²`, the light cone
  `lightCone p (2^k)` (radius of `evolve 2^(k-1)`, via `step_light_cone`) stays
  inside the domain covered by `c.toGrid (0,0)`. Pure Manhattan arithmetic, no
  `hashlifeResultAux`, no whnf wall — proven (`manhattan_deviation` Nat→Int
  bridge + power-normalization + pure-Int `linarith`).
- **S3 (sub-sorry)** : sub-cell coverage — the quadrant super-cell `q_j` whose
  centered region contains `p` agrees with `c.toGrid` on that light cone, so
  `evolve 2^(k-1) (c.toGrid) p = evolve 2^(k-1) (q_j.toGrid) p` by
  `step_light_cone (2^(k-1))`.
- **S4 (sub-sorry, core)** : assemble — combine S1+S2+S3 with the four
  `centralCorrect q_j (k-1)` facts from P4.3 (`p4_wave2_ih`) to conclude the
  pointwise membership agreement that `p4_succ_membership` needs.

Until S3–S4 are closed, `p4_half_steps_compose` remains the `True` placeholder
(it is consumed by `p4_succ_membership` only structurally); S1 (composition)
and S2 (no-leak) are now closed, so the remaining open surface is the
sub-cell-coverage + assembly argument (S3, S4). -/

/-- **S1** (CLOSED): `evolve (a + b) g = evolve a (evolve b g)`.

Pure function-iteration arithmetic — `evolve n g = step^[n] g`, so iteration
splits additively. The first closed milestone of the P4.4 balisage: the
composition `evolve 2^k = evolve 2^(k-1) ∘ evolve 2^(k-1)` is exactly
`evolve_add (2^(k-1)) (2^(k-1)) g`. -/
theorem evolve_add (a b : Nat) (g : Grid) :
    evolve (a + b) g = evolve a (evolve b g) := by
  induction a with
  | zero => simp [evolve_zero]
  | succ n ih =>
    rw [Nat.succ_add, evolve_succ, evolve_succ, ih]

/-- **S1 2^k instantiation** (CLOSED): `evolve 2^k = evolve 2^(k-1) ∘ evolve 2^(k-1)`.

The exact `2^k`-form of `evolve_add` (S1) that the glue `p4_succ_membership`
and the eventual P4.4 assemble step (S4) consume: the centered-window result of
`evolve 2^k` decomposes into two `evolve 2^(k-1)` half-steps (wave 1 then wave
2). Gated on `1 ≤ k` so that the predecessor `k-1` is well-defined as a `Nat`.
The power fact `2^k = 2^(k-1) + 2^(k-1)` is discharged in pure `Nat`
(`Nat.pow_succ` + `ring`); `omega` is avoided on the powers because it loses the
positivity of the `2^(k-1)` atom under the additive doubling (cf. the c.146
omega-limitation lesson on `window_cone_in_domain`). -/
theorem evolve_half_step (k : Nat) (hk : 1 ≤ k) (g : Grid) :
    evolve (2^k) g = evolve (2^(k-1)) (evolve (2^(k-1)) g) := by
  -- Introduce a fresh name `m` for the predecessor `k-1`. A plain
  -- `have hpred : k = (k-1) + 1` then `rw [hpred]` rewrites the `k` *inside*
  -- `2^(k-1)` too (since `k` appears in `k-1`), leaving atoms `2^(k-1)` vs
  -- `2^(1+(k-1)-1)` that `ring` cannot unify. `set` makes `m` opaque so
  -- `rw [hkm]` touches only the LHS-exponent `k`.
  set m := k - 1 with hm
  have hkm : k = m + 1 := by omega
  have h2pow : 2^k = 2^m + 2^m := by rw [hkm, Nat.pow_succ]; ring
  rw [h2pow, evolve_add]

/-- **S2 helper**: lift the `Nat` `manhattan` bound to per-coordinate `Int.abs`
    bounds. Isolated from `window_cone_in_domain` below so the cone/window
    reasoning works purely in `Int`: `omega` closes the `Nat.natAbs` goals here
    in isolation, but splits the `Nat` `2^k` atom from its `(2^k : Int)` cast
    when both appear in one goal (a known `omega` limitation on mixed
    `Nat`/`Int` atoms). -/
private theorem manhattan_deviation (p q : Int × Int) (R : Nat)
    (h : manhattan p q ≤ R) : |p.1 - q.1| ≤ (R : Int) ∧ |p.2 - q.2| ≤ (R : Int) := by
  -- Isolate the Nat `manhattan`/`natAbs` → `Int.abs` lifting from the
  -- power/window reasoning, so `window_cone_in_domain` below works purely in
  -- `Int` (omega handles `Int.abs` + powers cleanly, but struggles when
  -- `Nat.natAbs` and `Int.abs` of the same term share a goal).
  unfold manhattan at h
  have h1' : Int.natAbs (p.1 - q.1) ≤ R := by omega
  have h2' : Int.natAbs (p.2 - q.2) ≤ R := by omega
  refine ⟨?_, ?_⟩
  · rw [Int.abs_eq_natAbs]; exact_mod_cast h1'
  · rw [Int.abs_eq_natAbs]; exact_mod_cast h2'

/-- **S2** (CLOSED): the light cone does not leak out of the MacroCell domain.

    For a point `p` in the centered window `[2^k, 2^k + 2^(k+1))²` (the region
    the Hashlife result covers), any cell `q` within Manhattan distance `2^k`
    of `p` — i.e. any cell in the light cone `lightCone p (2^k)` (radius `2^k`
    is exactly the cone radius of `evolve 2^(k-1)` via `step_light_cone`) —
    stays inside the full MacroCell domain `[0, 2^(k+2))²`.

    This is the geometric core of the "boundary does not leak" half of P4.4:
    it is why the wave-2 super-cells, each computing `evolve 2^(k-1)` on its
    own grid, nonetheless agree with the global `evolve 2^k` on the centered
    window — every cell that could influence a centered point is still within
    the MacroCell's recorded domain. No `hashlifeResultAux`, no whnf wall —
    pure Manhattan arithmetic over `Int`, reusing `manhattan` (L85). The proof
    bridges via `manhattan_deviation`, proves the power facts `2^(k+1) = 2·2^k`
    and `2^(k+2) = 4·2^k` in pure `Nat` (rw + `Nat.pow_succ`), rewrites them in
    so everything is linear in the single atom `2^k`, and closes with `linarith`
    (`omega` loses the positivity of `2^k` under the multiplicative atoms). -/
private theorem window_cone_in_domain (k : Nat) (p q : Int × Int)
    (hp1_lo : (2^k : Int) ≤ p.1) (hp1_hi : p.1 < 2^k + 2^(k+1))
    (hp2_lo : (2^k : Int) ≤ p.2) (hp2_hi : p.2 < 2^k + 2^(k+1))
    (hc : manhattan p q ≤ 2^k) :
    (0 : Int) ≤ q.1 ∧ q.1 < 2^(k+2) ∧ (0 : Int) ≤ q.2 ∧ q.2 < 2^(k+2) := by
  -- Bridge the Nat `manhattan` bound to per-coordinate `Int` abs bounds, then
  -- unpack abs into linear inequalities (linarith does not split `|x|`).
  obtain ⟨hq1, hq2⟩ := manhattan_deviation p q (2^k) hc
  -- `manhattan_deviation` types its bound as `↑(2^k)` (Nat cast of the Nat
  -- radius), but the window hypotheses below use the native-Int `(2^k : Int)`
  -- (`HPow`). These are the same value but distinct terms, so `linarith` would
  -- see two unrelated atoms. Normalize via `Nat.cast_pow` to a single atom.
  have hk_pow : (↑((2:Nat)^k) : Int) = (2^k : Int) := Nat.cast_pow 2 k
  rw [hk_pow] at hq1 hq2
  obtain ⟨hq1lo, hq1hi⟩ := abs_le.mp hq1
  obtain ⟨hq2lo, hq2hi⟩ := abs_le.mp hq2
  -- Power facts proven in pure Nat (rw only — omega splits the Nat `2^k` from
  -- `Nat.pow_succ` against the `(2^k : Int)` casts in scope), lifted to Int.
  have hpe1 : (2^(k+1) : Int) = 2 * (2^k : Int) := by
    have h : (2 : Nat)^(k+1) = 2 * (2 : Nat)^k := by
      rw [show (k + 1 : Nat) = Nat.succ k from rfl, Nat.pow_succ, Nat.mul_comm]
    exact_mod_cast h
  have hpe2 : (2^(k+2) : Int) = 4 * (2^k : Int) := by
    have h1 : (2 : Nat)^(k+1) = 2 * (2 : Nat)^k := by
      rw [show (k + 1 : Nat) = Nat.succ k from rfl, Nat.pow_succ, Nat.mul_comm]
    have h2 : (2 : Nat)^(k+2) = 2 * (2 : Nat)^(k+1) := by
      rw [show (k + 2 : Nat) = Nat.succ (k + 1) from rfl, Nat.pow_succ, Nat.mul_comm]
    have h : (2 : Nat)^(k+2) = 4 * (2 : Nat)^k := by rw [h2, h1]; ring
    exact_mod_cast h
  -- Rewrite every power occurrence into a multiple of the single atom `2^k`,
  -- so the goal reduces to pure linear `Int` arithmetic in `2^k`. `linarith`
  -- (not `omega`) closes it: omega loses the positivity of `2^k` when juggling
  -- the `2^(k+1)`/`2^(k+2)` multiplicative atoms (counterexample: `2^k ≤ -1`),
  -- while `linarith` treats `2^k` as a plain linear variable, and the bounds
  -- `0 ≤ q.i`, `q.i < 4·2^k` follow from `p.i ∈ [2^k, 3·2^k)` and
  -- `|p.i - q.i| ≤ 2^k` with no sign assumption.
  rw [hpe1] at hp1_hi hp2_hi
  rw [hpe2]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals linarith

/-- **P4.4** (compositional, hardest): the two half-steps compose — wave 1
    (advancing `2^(k-1)` generations) followed by wave 2 (another `2^(k-1)`)
    equals `evolve (2^k)` on the centered window, because the boundary of
    each sub-cell does not leak into the live region (light-cone lemma P2,
    `step_light_cone`, proven above). Difficulty: P4.4 (research-level).

    **Balisage (c.145)**: decomposed into S1 (CLOSED, `evolve_add`) + S2/S3/S4
    sub-sorries — see the section docstring above. Until S2–S4 close, this
    remains the `True` placeholder consumed structurally by `p4_succ_membership`. -/
theorem p4_half_steps_compose
    (c : MacroCell) (k : Nat) (hwf : c.wf = true) (hk : c.level = k + 2) : True := by
  sorry

/-- **P4 entry point**: the pointwise membership biconditional for the
    inductive step. Glues `p4_double_nine_shape` (P4.1), `p4_wave1_ih`
    (P4.2), `p4_wave2_ih` (P4.3), and `p4_half_steps_compose` (P4.4). Once
    the four sub-lemmas are proven, this function produces the
    `∀ p, p ∈ ... ↔ p ∈ ...` hypothesis that `p4_ext_bridge` consumes.

    **Pointwise-proof balisage (c.147)** — the residual `sorry` after `intro p`
    is the pointwise form of the P4.4 sub-cell coverage (S3) + assemble (S4)
    argument, decomposed here into three named pieces:
    - **G1 (geometric, tractable)** — RHS reduction: `p ∈ restrictGridTo
      (evolve 2^k g) 2^k 2^(k+1)` splits via `mem_restrictGridTo` into window
      bounds `[2^k, 3·2^k)²` (since `2^k + 2^(k+1) = 3·2^k`) plus the cell-state
      `isAlive (evolve 2^k g) p`. Pure arithmetic, no `hashlifeResultAux`.
    - **G2 (whnf-hard)** — LHS reduction: `p ∈ (hashlifeResultAux (k+2) c).toGrid
      (2^k, 2^k)` agrees, on the containing quadrant `q_j`, with `evolve 2^(k-1)`
      on `q_j.toGrid`, via the four `centralCorrect q_j (k-1)` from `_h3` (P4.3).
      Touches `hashlifeResultAux` results → the c.139/142/143 whnf wall.
    - **G3 (whnf-hard assemble)** — combine G1 and G2 with `step_light_cone`
      (locality, radius `2·2^k`) and `evolve_half_step` (the `2^k` half-step
      `evolve 2^k = evolve 2^(k-1) ∘ evolve 2^(k-1)`, now closed): the local
      sub-cell computation equals the global `evolve 2^k` on the centered window.

    Of these, `evolve_half_step` (the G3 half-step composition) is closed;
    G1/G2/G3 themselves remain `sorry` because they compose `hashlifeResultAux`
    results (the whnf-hard core, reserved for dedicated multi-cycle effort). -/
noncomputable def p4_succ_membership
    (c : MacroCell) (k : Nat) (hwf : c.wf = true) (hk : c.level = k + 2) (hk1 : 1 ≤ k)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j) :
    ∀ p, p ∈ (hashlifeResultAux (k + 2) c).toGrid ((2^k : Nat), (2^k : Nat)) ↔
        p ∈ restrictGridTo (evolve (2^k) (c.toGrid (0, 0))) (2^k : Int) (2^(k+1)) := by
  have _h1 := p4_double_nine_shape c k hwf hk
  have _h2 := p4_wave1_ih c k hwf hk hk1 ih
  have _h3 := p4_wave2_ih c k hwf hk hk1 ih
  have _h4 := p4_half_steps_compose c k hwf hk
  intro p
  -- LHS assembly (c.156). The 3 G3 gates (hcnode, hashlifeResultAux_succ_node,
  -- if_neg) now compose through the whnf wall, exposing the `node out_*`
  -- constructor and decomposing it via `mem_toGrid_node`.
  -- Destruct c via _h1 (p4_double_nine_shape: c = node(node×4)×4 ∧ 16 facts).
  obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, _hcshape⟩ := _h1
  obtain ⟨hcnode, hfacts⟩ := _hcshape
  -- Rewrite the input cell to its 16-grandchild node, then iota-reduce hRA.
  rw [hcnode]
  rw [show (k + 2) = (k + 1) + 1 from by omega]
  rw [hashlifeResultAux_succ_node]
  -- The if-condition (node16).level == 2 is FALSE for k >= 1 (level = k+2 >= 3).
  -- Discharge via the clean-context helper (opaque binders, c.139/c.143 pattern):
  -- applying it here keeps the level term inferred, never whnf-re-elaborated.
  have hne2 := node16_level_ne_two k hk1
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hfacts.1
  rw [if_neg hne2]
  -- LHS is now `p ∈ (node out_nw out_ne out_sw out_se).toGrid (2^k, 2^k)`;
  -- `mem_toGrid_node` (G3) decomposes it into the four quadrant memberships.
  rw [mem_toGrid_node]
  -- RESIDUAL (the offset-matching assembly): each `out_*.toGrid (off_*, off_*)`
  -- must be characterized via `centralCorrect_mem` (G2 congruence, crossing the
  -- whnf wall on the composed result) + the induction hypothesis `centralCorrect
  -- q_* (k-1)` from `_h3`, then bridged to the RHS window via `evolve_half_step`
  -- (the `2^k` half-step) + `evolve_add` (G1). The offsets `2^out_*.level` vs
  -- `2^k` and the ih at level (k-1) vs goal at level k are the matching core.
  sorry

/-- For a level-`k` MacroCell `c` with `k ≥ 2`, the centered region of
    `hashlifeResultAux (k+2) c` (viewed at offset `(2^k, 2^k)`) equals
    `evolve (2^k)` applied to `c.toGrid (0, 0)` and restricted to the
    centered `[2^k, 2^k + 2^(k+1)) × [2^k, 2^k + 2^(k+1))` region.

    **Statement correction**: offset `(2^k, 2^k)` accounts for centering.

    **Proof strategy** (P4, difficulty: hard, compositional):
    Strong induction on `k`.
    - Base `k = 0`: `hashlifeResultAux 2 c` reduces to `step4x4 c`, which
      is the direct B3/S23 computation on a 4x4 grid. The centered 2x2
      result at offset `(1, 1)` matches `evolve 1` restricted to `[1,3)×[1,3)`.
    - Inductive step `k → k+1`: the recursive Hashlife makes 9 sub-calls on
      level-`(k+1)` cells, then 4 sub-calls on the resulting level-`k`
      supercells. Each sub-call uses the IH at level `k`. The composition
      matches `step^[2^(k+1)]` by the light-cone lemma P2 applied 2^(k-1)
      times (once per "half-step" in the double-nine decomposition). -/
theorem hashlifeResult_central_correct (c : MacroCell) (k : Nat)
    (hwf : c.wf = true) (hk : c.level = k + 2) :
    let result := hashlifeResultAux (k + 2) c
    let resultGrid := result.toGrid ((2^k : Nat), (2^k : Nat))
    let expected := evolve (2^k) (c.toGrid (0, 0))
    resultGrid = restrictGridTo expected (2^k : Int) (2^(k+1)) := by
  -- P4 TARGET: central Hashlife correctness, by STRONG induction on the level
  -- index `k`. The motive quantifies over `c` (reverted before induction) so
  -- the induction hypothesis `ih` ranges over every MacroCell at a smaller
  -- level (not just a fixed `c`): this is required because the recursive step
  -- applies the IH to the double-nine *sub-cells* `n_i` of `c`, which are
  -- MacroCells distinct from `c` itself. A plain `cases k` exposes no such
  -- cross-cell IH, which (c.137) forced `p4_wave1_ih` to stay a vacuous `True`
  -- placeholder to avoid a forbidden mutual-recursion cycle. Threading `ih`
  -- down through `p4_succ_membership` -> `p4_wave1_ih` breaks that cycle (c.138),
  -- and the c.139 helper `p4_wave1_ih_step` makes the `ih` application compile.
  revert c hwf hk
  induction k using Nat.strongRecOn with
  | ind n ih =>
    intro c hwf hk
    cases n with
    | zero => exact hashlifeResult_central_correct_base c hwf hk
    | succ k =>
      have hk1 : 1 ≤ k + 1 := by omega
      exact p4_ext_bridge c (k + 1)
        (p4_succ_membership c (k + 1) hwf hk hk1
          (fun c' j hj hc'w hc'l => ih j hj c' hc'w hc'l))

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

**Residual obstacle chain (4 `sorry` total: L2471, L2536, L2853, L2862).**

  `p5_large_n_jump`            (L2852, re-signed to real target — proof body `sorry` at L2853)
    └→ `hashlifeResult_central_correct`  (L2555 — P4 entry point)
         └→ inductive `succ k` arm of P4 — residual `sorry`s:
              · `p4_half_steps_compose`  (L2470, P4.4 placeholder `True` — see note)
              · wave-glue residual       (L2536, succ-arm composition)
            (the shape/IH sub-lemmas `p4_double_nine_shape` L1744, `p4_wave1_ih_step`
            L2108, `p4_wave2_ih_step` L2146 carry no `sorry` in the current file)

The P4 inductive step is **research-level, multi-cycle**. The base case `k = 0`
of P4 is already fully proven (`hashlifeResult_central_correct_base`, L1648,
shape lemmas + `2^16` `native_decide`).

**Note on `p4_half_steps_compose` (L2470, P4.4).** The pure evolve half-step
composition is already closed (`evolve_add` L2353, `evolve_half_step` L2370), so
re-signing this placeholder to a raw-evolve statement would be vacuously provable
(gaming the sorry count). The genuine P4.4 content — the hashlife wave
decomposition on the centered window — is the wave-glue residual at L2536. So
`p4_half_steps_compose` is, as stated, redundant: its honest treatment is either
deletion (sorry 4→3) or a re-statement tied to the hashlife wave structure
(coordinator call). Left as `True` placeholder pending that call.

**Independently provable sub-claim (sorry-free additive grain, P4-free).**

The proof plan states "the jump expands the bounding box by at most `2^(k-2)`,
within the padding margin", so the claim

  `BoxAssezGrand g n → n ≥ jumpSize ... → BoxAssezGrand (jumpResult g) (n - jumpSize ...)`

is a purely geometric/arithmetic statement on the `box_assez_grand` predicate.
It does **not** depend on `hashlifeResult_central_correct` and can be discharged
via decidable evaluation + `Nat` arithmetic. This is a natural next sorry-free
additive grain on the P5.2 frame, queueable behind the P4 verrou unlock.

**Re-signed target (N2, 2026-07-09).** `p5_large_n_jump` (L2852) now carries the
real conclusion

  `(h : BoxAssezGrand g n) (hbig : n ≥ jumpSize (gridToMacroCellWithOffset g).2.level) →`
  `  evolveHashlifeFast n g = evolve n g`

with the proof body still `sorry` (L2853) pending the P4 unlock. The obstacle
remains structural-on-P4, not local-on-P5. -/

/-- **P5.2** (compositional, blocked on P4): when `n ≥ 2^(k-2)`,
    `evolveHashlifeFast n g` makes one Hashlife jump of `2^(k-2)` generations
    (certified equal to `evolve (2^(k-2))` by P4, `hashlifeResult_central_correct`),
    then recurses on `n - 2^(k-2)`. The light-cone lemma P2
    (`step_light_cone`, proven) guarantees the jump does not leak boundary
    cells into the live region, and `box_assez_grand` is preserved through the
    recursion. Difficulty: P5.2 (research-level; **blocked until P4
    inductive step proven**). -/
theorem p5_large_n_jump (n : Nat) (g : Grid) (h : BoxAssezGrand g n)
    (hbig : n ≥ jumpSize (gridToMacroCellWithOffset g).2.level) :
    evolveHashlifeFast n g = evolve n g := by
  sorry

/-- **P5.3** (glue): the full induction on `n`, with a case split on
    `n < 2^(k-2)` (P5.1) vs `n ≥ 2^(k-2)` (P5.2). Stays `sorry` until both
    sub-lemmas are proven. -/
theorem p5_inductive_step (n : Nat) (g : Grid) (h : BoxAssezGrand g n) :
    evolveHashlifeFast n g = evolve n g := by
  by_cases hsmall : n < jumpSize (gridToMacroCellWithOffset g).2.level
  · exact p5_small_n_fallback n g hsmall
  · sorry


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
