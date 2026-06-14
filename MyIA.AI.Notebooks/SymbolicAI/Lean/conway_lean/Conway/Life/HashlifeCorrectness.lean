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

/-- Membership in a restricted grid: in the grid and inside the window. -/
theorem mem_restrictGridTo {g : Grid} {lo : Int} {size : Nat} {p : Int × Int} :
    p ∈ restrictGridTo g lo size ↔
      p ∈ g ∧ lo ≤ p.1 ∧ p.1 < lo + (size : Int) ∧
        lo ≤ p.2 ∧ p.2 < lo + (size : Int) := by
  simp [restrictGridTo, List.mem_filter, and_assoc]

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
  -- P4 TARGET: central Hashlife correctness, by induction on level.
  -- Base case k = 0 holds in full generality (shape lemmas + 2^16
  -- native_decide). `p4_ext_bridge` discharges the canonical-list
  -- bookkeeping of the remaining arm: the goal left is the pointwise
  -- membership biconditional, where the light-cone (P2) and double-nine
  -- decomposition arguments live.
  cases k with
  | zero => exact hashlifeResult_central_correct_base c hwf hk
  | succ k => exact p4_ext_bridge c (k + 1) (fun p => by sorry)

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
  -- Inductive step (fallback + jump): open.
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
