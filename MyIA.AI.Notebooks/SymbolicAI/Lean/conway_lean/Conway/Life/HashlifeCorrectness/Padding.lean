/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway.Life.HashlifeCorrectness.Padding

Sub-module of `Conway.Life.HashlifeCorrectness`. Phase 3b multi-agent
prover targets (Epic #1453). Scope: /-! ## P1. Padding predicate
was byte-identically displaced from the original monolith at PR A of
#9863 (po-2023, dispatch ai-01 2026-08-07T12:20:37Z).

Proof bodies are unchanged — only framing (imports, namespace opens,
this docstring) is added. The 38 allow-axioms names referenced by the
audit job in `.github/workflows/lean-conway.yml` depend only on the
`Conway.Life.*` namespace prefix, NOT on intermediate namespaces or
file paths — so the allow-list stays byte-identical across the split.
-/

import Conway.Life
import Conway.Life.GridCanonical
import Conway.Life.MacroCell
import Conway.Life.Hashlife
import Conway.Life.ConeGeometry

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

/-! ### n-aware margin predicate (`box_assez_grandN`) — P5 redesign gate N1

The n-aware dual of `box_assez_grand` over `gridFrameN n g` (padding `max 2 n`,
see `MacroCell.gridFrameN`). Unlike the fixed-`gridFrame` version — which is
unsatisfiable for `n > 2` (`boxAssezGrand_nonempty_le_two`) — this predicate is
satisfiable for `n` arbitrarily large, because the `max 2 n` padding guarantees
each live cell `max 2 n ≥ n` cells of margin by construction. The witnesses
below exhibit `n = 3 > 2` for the single-cell grid: `box_assez_grandN` holds
where `box_assez_grand` provably fails — the concrete dual of the unsat cap
that `gridFrameN` breaks (issue #3846). -/

/-- The "box assez grand" predicate over the n-aware frame `gridFrameN n g`
    (light-cone margin `≥ n` on all four sides), n-aware analog of
    `box_assez_grand`. -/
def box_assez_grandN (g : Grid) (n : Nat) : Bool :=
  let ((r0, c0), lvl) := gridFrameN n g
  let sz : Int := 2^lvl
  g.all (fun (r, c) => cellMargin r0 c0 sz n r c)

/-- Propositional version of `box_assez_grandN` for theorem statements. -/
def BoxAssezGrandN (g : Grid) (n : Nat) : Prop := box_assez_grandN g n = true

/-- Decidability of the propositional `BoxAssezGrandN` (gate W2, issue #3846).
    Lifted from the decidable Boolean equation `box_assez_grandN g n = true`, so
    that the non-vacuity of the n-aware predicate can be discharged by
    `native_decide` directly on the `BoxAssezGrandN g n` proposition (the form
    used as the hypothesis of `hashlife_correctN` below). -/
instance (g : Grid) (n : Nat) : Decidable (BoxAssezGrandN g n) :=
  inferInstanceAs (Decidable (box_assez_grandN g n = true))

/-- **Box coincidence for `n ≤ 2` (N3 threading infrastructure, issue #3846).**
    On the small-`n` regime, the n-aware frame `gridFrameN n g` coincides with
    the fixed frame `gridFrame g` (`gridFrameN_le_two_eq_gridFrame`), so the two
    margin predicates — which differ only in which frame feeds the
    `cellMargin` bound — are equal. This bridges the n-aware hypothesis
    `BoxAssezGrandN` to the fixed-frame `BoxAssezGrand` consumed by the already
    proven `hashlife_correct`, letting the N-version spec's small-`n` arm be
    discharged without re-proving `hashlife_correct` on the n-aware frame. -/
theorem box_assez_grandN_le_two_eq (n : Nat) (g : Grid) (hn : n ≤ 2) :
    box_assez_grandN g n = box_assez_grand g n := by
  unfold box_assez_grandN box_assez_grand
  rw [gridFrameN_le_two_eq_gridFrame n g hn]

/-- Anti-vacuity witness (dual of the `boxAssezGrand_nonempty_le_two` unsat
    cap): the n-aware predicate `box_assez_grandN` is *satisfiable* for
    `n = 3 > 2` on the single-cell grid. With `gridFrameN 3 [(0,0)]` the
    padding is `max 2 3 = 3`, giving margin `3 ≥ 3` on every side, so the
    large-`n` light-cone hypothesis holds where the fixed-2 `gridFrame` could
    not (issue #3846, gate N1). -/
theorem box_assez_grandN_single_cell_3 : box_assez_grandN [(0, 0)] 3 = true := by
  native_decide

/-- **Universal large-`n` non-vacuity (gate W1, issue #3846)**: the n-aware
    predicate `box_assez_grandN` holds for the single-cell grid at *every* `n`.
    This is the constructive dual of the `boxAssezGrand_nonempty_le_two` unsat
    cap: the fixed frame forces `n ≤ 2`, the n-aware frame `gridFrameN` admits
    every `n` because it pads by `max 2 n ≥ n` on all sides. The single-cell
    extremes are all `0`, so the frame offset is `-(max 2 n)`; after unfolding,
    the four `cellMargin` bounds reduce to `n ≤ max 2 n` (top/left, free from
    `le_max_right`) and `max 2 n + n < 2^lvl` (bottom/right), where
    `2^lvl ≥ 1 + 2·(max 2 n) ≥ (max 2 n) + n + 1` by `ceilLog2_spec`. The
    `Int`/`Nat`-cast between the goal's `(2 : Int) ^ lvl` and the `Nat` spec is
    bridged by `exact_mod_cast`. -/
theorem box_assez_grandN_single_cell (n : Nat) : box_assez_grandN [(0, 0)] n = true := by
  have hrMin : gridRowMin [(0, 0)] = 0 := by native_decide
  have hrMax : gridRowMax [(0, 0)] = 0 := by native_decide
  have hcMin : gridColMin [(0, 0)] = 0 := by native_decide
  have hcMax : gridColMax [(0, 0)] = 0 := by native_decide
  simp only [box_assez_grandN, gridFrameN, hrMin, hrMax, hcMin, hcMax,
      List.all_cons, List.all_nil, Bool.and_true, max_self, Int.sub_self]
  set pad := max 2 n with hpad
  set side := (0 + 1 + 2 * (pad : Int)).toNat
  have hpn : n ≤ pad := le_max_right 2 n
  have hside : side = 1 + 2 * pad := by omega
  have hspec : 2 ^ ceilLog2 side ≥ side := ceilLog2_spec side
  have hbig : (2 : Int) ^ ceilLog2 side ≥ pad + n + 1 := by
    have hnat : 2 ^ ceilLog2 side ≥ pad + n + 1 := by omega
    exact_mod_cast hnat
  rw [cellMargin_true_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Honest contrast: the *fixed-`gridFrame`* predicate provably *fails* for the
    same grid at `n = 3` — confirming the duality is non-vacuous
    (`box_assez_grandN` breaks exactly what `box_assez_grand` cannot satisfy). -/
theorem box_assez_grand_single_cell_3_false : box_assez_grand [(0, 0)] 3 = false := by
  native_decide

/-! #### Large-`n` non-vacuity (P5 redesign gate W1, issue #3846)

The `n = 3` witnesses above only exhibit non-vacuity at the exact threshold
where the fixed frame fails. The P5 large-`n` correctness target is only
*meaningful* when the padding hypothesis is satisfiable at large `n`: restating
`hashlife_correct` over `BoxAssezGrandN` (the n-aware frame) is vacuous unless
`BoxAssezGrandN g n` is realizable for `n ≥ 8`. The `native_decide` witnesses
below exhibit this concretely at `n = 8` — exactly the regime where the
fixed-frame `box_assez_grand` is unsatisfiable (`n ≤ 2` cap of
`boxAssezGrand_nonempty_le_two`) — on the single-cell grid and on the canonical
`block` / `glider` patterns. Because `gridFrameN n g` pads by `max 2 n ≥ n` on
every side, every live cell carries margin `≥ n` *by construction*, so
`box_assez_grandN` holds at any `n` (the constructive universal
`∀ n, box_assez_grandN [(0,0)] n = true` is the natural next target — it bridges
through `cellMargin_true_iff` to the four margin bounds discharged by
`ceilLog2_spec` + `omega`, the exact dual of `boxAssezGrand_nonempty_le_two`;
slated for a focused cycle, as the `Int`/`Nat`-cast elaboration of the
`gridFrameN` term needs interactive development). -/

/-- Concrete large-`n` non-vacuity witness (gate W1): `box_assez_grandN` holds at
    `n = 8` on the single-cell grid — exactly the regime where the fixed-frame
    `box_assez_grand` is unsatisfiable (`n = 8 > 2`). -/
theorem box_assez_grandN_single_cell_8 : box_assez_grandN [(0, 0)] 8 = true := by
  native_decide

/-- Large-`n` non-vacuity on a real still-life: the 2×2 `block` carries margin
    `≥ 8` on every side under `gridFrameN 8` (padding `max 2 8 = 8`), so the
    n-aware predicate holds at `n = 8` where `box_assez_grand block 8` cannot
    (gate W1). -/
theorem box_assez_grandN_block_8 : box_assez_grandN block 8 = true := by
  native_decide

/-- Large-`n` non-vacuity on a real spaceship: the `glider` (3×3 bounding box)
    carries margin `≥ 8` on every side under `gridFrameN 8`, so the n-aware
    predicate holds at `n = 8` (gate W1). -/
theorem box_assez_grandN_glider_8 : box_assez_grandN glider 8 = true := by
  native_decide

/-- Honest contrast at the large-`n` regime: the fixed-`gridFrame` predicate
    provably *fails* at `n = 8` (the `n ≤ 2` cap of
    `boxAssezGrand_nonempty_le_two`), confirming the n-aware predicate breaks
    exactly what the fixed one cannot satisfy. -/
theorem box_assez_grand_single_cell_8_false : box_assez_grand [(0, 0)] 8 = false := by
  native_decide

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

/-! ### Structural satisfiability bound (N1 audit, 2026-07-09)

The sanity witnesses below (`BoxAssezGrand block 2`, glider, blinker, …)
observe that the strengthened predicate only holds for `n ≤ 2` on the
canonical patterns. The lemmas of this section prove that this bound is
**structural in `gridFrame`, not pattern-specific**: for *every* non-empty
grid, `gridFrame` anchors the domain at `r0 := rMin - 2` (fixed 2-cell
padding), so the topmost live cell has top margin exactly `2`, and
`cellMargin` demands `r0 + n ≤ r` — hence `BoxAssezGrand g n → n ≤ 2`.

Meanwhile `gridFrame` picks `side ≥ 5` (1-cell bounding box + 4 padding), so
the MacroCell level is ≥ 3 and `jumpSize = 2^lvl ≥ 8`. Consequences for the
P5.2 plan (see the obstacle scan before `p5_large_n_jump`):

- the hypotheses of `p5_large_n_jump` (`BoxAssezGrand g n` **and**
  `n ≥ jumpSize …`) are **jointly unsatisfiable on non-empty grids**
  (`p5_large_n_hyps_unsat` below) — the large-`n` arm of `p5_inductive_step`
  is reachable only for `g = []`;
- the sketched N1 frame lemma ("the jump preserves `BoxAssezGrand` through
  the recursion") is **vacuous as stated** — same trap as the deleted
  `p4_half_steps_compose` placeholder (N2-bis, G.2 gaming);
- a `padGrid`-style helper adding live sentinel cells (the N5 sketch) cannot
  fix satisfiability: whichever cell ends up topmost after padding *still*
  has top margin exactly `2` by construction of `gridFrame`. The honest
  unlock is a `gridFrame`/`box_assez_grand` redesign (e.g. padding parameter
  dependent on `n`) — design gate, ai-01.

These lemmas are *diagnostic*: like `box_assez_grand_not_vacuous` (c.148),
they document a geometric property of the current definitions so the P5 plan
can be re-scoped honestly instead of closed vacuously. -/

/-- **Structural cap on the padding parameter**: for any non-empty grid,
    `BoxAssezGrand g n` forces `n ≤ 2`. The topmost live cell (witnessed by
    `gridRowMin_mem`) has top margin exactly `2` in the frame chosen by
    `gridFrame` (`r0 = rMin - 2`), and `cellMargin` requires `r0 + n ≤ r`. -/
theorem boxAssezGrand_nonempty_le_two (g : Grid) (n : Nat)
    (hg : g ≠ []) (h : BoxAssezGrand g n) : n ≤ 2 := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    obtain ⟨p, hp, hmin⟩ := gridRowMin_mem (p₀ :: ps) (List.cons_ne_nil p₀ ps)
    unfold BoxAssezGrand at h
    simp only [box_assez_grand, gridFrame, List.all_eq_true] at h
    obtain ⟨r, c⟩ := p
    obtain ⟨h1, _h2, _h3, _h4⟩ :=
      (cellMargin_true_iff _ _ _ _ _ _).mp (h (r, c) hp)
    -- h1 : gridRowMin (p₀ :: ps) - 2 + n ≤ r, and hmin : r = gridRowMin (p₀ :: ps)
    simp only at hmin
    omega

/-- Arithmetic helper: `ceilLog2 s ≥ 3` as soon as `s ≥ 5` (since
    `2^2 = 4 < 5 ≤ 2^(ceilLog2 s)` by `ceilLog2_spec`). -/
theorem ceilLog2_ge_three_of_ge_five (s : Nat) (h5 : 5 ≤ s) :
    3 ≤ ceilLog2 s := by
  by_contra hlt
  push_neg at hlt
  have hspec : s ≤ 2 ^ ceilLog2 s := ceilLog2_spec s
  have hle : 2 ^ ceilLog2 s ≤ 2 ^ 2 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The MacroCell level chosen by `gridToMacroCellWithOffset` is the
    `gridFrame` level (the builder preserves the requested level,
    `level_buildFromGrid`). -/
theorem gridToMacroCellWithOffset_level (g : Grid) :
    (gridToMacroCellWithOffset g).2.level = (gridFrame g).2 := by
  rcases hfg : gridFrame g with ⟨⟨r0, c0⟩, lvl⟩
  simp only [gridToMacroCellWithOffset, hfg, level_buildFromGrid]

/-- For any non-empty grid, the `gridFrame` level is at least `3`: the frame
    side is `max height width ≥ 5` (inclusive bounding box + 4 cells of
    padding), and `ceilLog2 5 = 3`. -/
theorem gridFrame_level_ge_three (g : Grid) (hg : g ≠ []) :
    3 ≤ (gridFrame g).2 := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    have hrr : gridRowMin (p₀ :: ps) ≤ gridRowMax (p₀ :: ps) :=
      gridRowMin_le_gridRowMax _ (List.cons_ne_nil _ _)
    simp only [gridFrame]
    apply ceilLog2_ge_three_of_ge_five
    have h5 : 5 ≤ (gridRowMax (p₀ :: ps) - gridRowMin (p₀ :: ps) + 5).toNat := by
      omega
    omega

/-- For any non-empty grid, the Hashlife jump is at least `8` generations:
    the `gridFrame` level is ≥ 3 (`gridFrame_level_ge_three`) and
    `jumpSize lvl = 2^lvl` is monotone. -/
theorem jumpSize_gridLevel_ge_eight (g : Grid) (hg : g ≠ []) :
    8 ≤ jumpSize (gridToMacroCellWithOffset g).2.level := by
  rw [gridToMacroCellWithOffset_level]
  have h3 : 3 ≤ (gridFrame g).2 := gridFrame_level_ge_three g hg
  unfold jumpSize
  calc (8 : Nat) = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (gridFrame g).2 := Nat.pow_le_pow_right (by norm_num) h3

/-- **The P5.2 hypotheses are jointly unsatisfiable on non-empty grids.**
    `BoxAssezGrand g n` caps `n ≤ 2` (`boxAssezGrand_nonempty_le_two`) while
    the jump guard requires `n ≥ jumpSize ≥ 8` (`jumpSize_gridLevel_ge_eight`).
    See the section docstring: closing the P5 sorries through this vacuity
    would prove `hashlife_correct` without any Hashlife jump ever being
    exercised — the theorem statement needs a satisfiability redesign first. -/
theorem p5_large_n_hyps_unsat (g : Grid) (n : Nat) (hg : g ≠ [])
    (h : BoxAssezGrand g n)
    (hbig : n ≥ jumpSize (gridToMacroCellWithOffset g).2.level) : False := by
  have h2 := boxAssezGrand_nonempty_le_two g n hg h
  have h8 := jumpSize_gridLevel_ge_eight g hg
  omega

end Life
end Conway
