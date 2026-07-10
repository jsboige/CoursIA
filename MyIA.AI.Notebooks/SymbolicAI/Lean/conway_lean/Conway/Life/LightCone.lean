/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Light-cone geometry (Conway Game of Life)

Sorry-free geometric lemmas about `manhattan` and `lightCone` (defined in
`Conway.Life.HashlifeCorrectness`). These bridge facts make the light-cone
machinery composable: they are NOT new locality results (the fundamental
locality theorem `step_light_cone` is proven in `HashlifeCorrectness`), but
the elementary set/arithmetic relationships between cones of different radii
and between Manhattan and per-coordinate bounds, which future correctness
proofs chain across the `evolve` recursion.

The central fact formalized here is the **Game-of-Life speed-of-light
principle** (commented in `HashlifeCorrectness` P2 §, L497-504, but not
previously stated as a theorem): over `t` generations information travels at
Chebyshev radius `t` (one Moore-neighborhood step per generation), and the
Chebyshev ball of radius `t` is contained in the Manhattan ball of radius
`2*t` (the corner cell `(p.1 ± t, p.2 ± t)` is at Manhattan distance `2*t`).
This containment is exactly why `step_light_cone` demands agreement on
`lightCone p (2 * t)` — that radius is the *tight* GoL influence bound, not a
loose over-approximation.

Epic #3846 (Hashlife correctness infrastructure). All `sorry`s eliminated at
creation.
-/

import Conway.Life.HashlifeCorrectness

namespace Conway
namespace Life

/-! ## Monotonicity: larger radius → larger cone

A light cone of radius `t₁` is contained in the light cone of any larger
radius `t₂ ≥ t₁`. This follows directly from the membership characterization
(`mem_lightCone_of_manhattan_le` / `manhattan_le_of_mem_lightCone`): a cell in
the smaller cone is at Manhattan distance `≤ t₁ ≤ t₂`, hence in the larger
cone. -/
theorem lightCone_subset_of_le (p : Int × Int) {t₁ t₂ : Nat} (h : t₁ ≤ t₂) :
    lightCone p t₁ ⊆ lightCone p t₂ := by
  intro q hq
  exact mem_lightCone_of_manhattan_le p q t₂
    ((manhattan_le_of_mem_lightCone p q t₁ hq).trans h)

/-! ## Per-coordinate bound: membership bounds each coordinate

A cell in `lightCone p t` has each coordinate within `t` of `p`'s
corresponding coordinate. This is the "Manhattan-`t` ⊆ Chebyshev-`t`"
direction (each coordinate's displacement is bounded by the total Manhattan
distance). -/
theorem coord_bound_of_mem_lightCone (p q : Int × Int) (t : Nat)
    (h : q ∈ lightCone p t) :
    Int.natAbs (p.1 - q.1) ≤ t ∧ Int.natAbs (p.2 - q.2) ≤ t := by
  have hm : manhattan p q ≤ t := manhattan_le_of_mem_lightCone p q t h
  unfold manhattan at hm
  refine ⟨?_, ?_⟩ <;> omega

/-! ## Speed-of-light principle: Chebyshev-`t` ⊆ Manhattan-`2*t`

The converse direction that makes `2*t` the **tight** GoL radius. If each
coordinate of `q` is within `t` of `p` (Chebyshev distance `≤ t`) — the exact
region a single B3/S23 step can reach in one generation, lifted to `t` steps
— then the Manhattan distance is `≤ 2*t`, so `q ∈ lightCone p (2 * t)`.

This is the formal justification for `step_light_cone`'s `2 * t` radius: the
Moore-neighborhood influence of one generation has Chebyshev radius `1`, so
`t` generations reach Chebyshev radius `t`, and that Chebyshev ball is
contained in the Manhattan ball of twice the radius. The factor `2` is
tight (the diagonal neighbor is at Manhattan distance `2`). -/
theorem mem_lightCone_of_chebyshev_le (p q : Int × Int) (t : Nat)
    (h1 : Int.natAbs (p.1 - q.1) ≤ t) (h2 : Int.natAbs (p.2 - q.2) ≤ t) :
    q ∈ lightCone p (2 * t) := by
  apply mem_lightCone_of_manhattan_le p q (2 * t)
  unfold manhattan
  omega

/-! ## Translation invariance: shifting the center shifts the cone

The light cone is translation-equivariant: membership of `q` in `lightCone p t`
depends only on the displacement `q - p`, not on the absolute position `p`. This
is the Grid-level counterpart of the `toGrid` offset-shift machinery in
`HashlifeCorrectness` (`toGrid_shift`, `toGrid_shift_between`), and is the
structural fact needed to relate the light cone before and after a `hashlifeJump`
shifts the grid by `jumpResultOff` in `evolveHashlifeFastAux`. The cone is an
isometry of the Manhattan metric, so its shape is preserved under translation. -/
theorem lightCone_translate (p q : Int × Int) (t : Nat) :
    q ∈ lightCone p t ↔ (q.1 - p.1, q.2 - p.2) ∈ lightCone (0, 0) t := by
  constructor
  · intro h
    apply mem_lightCone_of_manhattan_le (0, 0) _ t
    have hm := manhattan_le_of_mem_lightCone p q t h
    unfold manhattan at *; omega
  · intro h
    apply mem_lightCone_of_manhattan_le p q t
    have hm := manhattan_le_of_mem_lightCone (0, 0) _ t h
    unfold manhattan at *; omega

/-! ## Chebyshev (chessboard) distance and the tight locality cone

The *tight* Game-of-Life locality is governed by the Chebyshev (L∞) distance:
one B3/S23 generation reaches exactly the Moore neighborhood (Chebyshev radius
1), so `t` generations reach Chebyshev radius `t`. The `lightCone` machinery
above uses the Manhattan (L1) distance, which over-approximates the tight reach
by a factor of 2 — `step_light_cone` demands Manhattan radius `2 * t`. The
lemmas below formalize the Chebyshev cone structure that a *tight* single-jump
correctness proof chains through:

- the cone fits in a margin-`t` box (**margin sufficiency** — the geometric fact
  that makes the `padCenter2` margin `2^k` sufficient for a single jump of `2^k`
  generations: the tight Chebyshev reach `2^k` fits exactly in a margin-`2^k`
  box, whereas the loose Manhattan-`2^k` light cone would need `2^(k+1)`); and
- the tight cone is contained in the loose Manhattan-`2*t` light cone.

These are the elementary distance facts; they do not yet assert anything about
`evolve` (the locality statement `step_light_cone` lives in `HashlifeCorrectness`).
Epic #3846 (Hashlife correctness infrastructure, N2 tight-locality groundwork). -/

/-- Chebyshev (chessboard / L∞) distance between two cells: the larger of the
    absolute coordinate displacements. -/
def chebDist (p q : Int × Int) : Nat :=
  max (Int.natAbs (q.1 - p.1)) (Int.natAbs (q.2 - p.2))

/-- Reflexivity: a cell is at Chebyshev distance 0 from itself. -/
theorem chebDist_self (p : Int × Int) : chebDist p p = 0 := by
  unfold chebDist; omega

/-- Symmetry: the Chebyshev distance is invariant under swapping the two cells. -/
theorem chebDist_comm (p q : Int × Int) : chebDist p q = chebDist q p := by
  unfold chebDist; omega

/-- Monotonicity in the radius: a larger radius weakly contains the cone. -/
theorem chebDist_le_trans {t₁ t₂ : Nat} (h : t₁ ≤ t₂) {p q : Int × Int}
    (hd : chebDist p q ≤ t₁) : chebDist p q ≤ t₂ := hd.trans h

/-- Margin sufficiency: a cell within Chebyshev radius `t` of `p` lies in the
    margin-`t` box — each coordinate is within `t` of `p`'s coordinate. This is
    the geometric reason a box margin of `t` (e.g. `padCenter2`'s `2^k` margin
    at a level advancing `2^k` generations) covers the *tight* Chebyshev-`t`
    reach, even though that same margin `t` does not cover the *loose*
    Manhattan-`t` light cone (which reaches `2 * t`). -/
theorem coord_bound_of_chebDist_le (p q : Int × Int) (t : Nat)
    (h : chebDist p q ≤ t) :
    Int.natAbs (q.1 - p.1) ≤ t ∧ Int.natAbs (q.2 - p.2) ≤ t := by
  unfold chebDist at h
  omega

/-- Tight ⊆ loose (distance form): Chebyshev radius `t` is bounded by Manhattan
    radius `2 * t`, because each coordinate displacement is `≤ t` and the
    Manhattan distance is their sum. -/
theorem manhattan_le_of_chebDist_le (p q : Int × Int) (t : Nat)
    (h : chebDist p q ≤ t) : manhattan p q ≤ 2 * t := by
  unfold chebDist at h
  unfold manhattan
  omega

/-- A cell within Chebyshev radius `t` lies in the Manhattan-`(2*t)` light cone.
    This is the bridge from the tight Chebyshev reach to the loose
    `lightCone p (2 * t)` radius that `step_light_cone` operates on. -/
theorem mem_lightCone_of_chebDist_le (p q : Int × Int) (t : Nat)
    (h : chebDist p q ≤ t) : q ∈ lightCone p (2 * t) :=
  mem_lightCone_of_manhattan_le p q (2 * t) (manhattan_le_of_chebDist_le p q t h)

/-! ## Chebyshev triangle inequality and cone growth by a Moore step

The foundational metric fact (`chebDist_triangle`) and the **tight-cone growth
theorem** named by ai-01's N2 greenlight: a cell lies in the Chebyshev-`(t+1)`
cone of `p` iff one can reach it from the Chebyshev-`t` cone via a single Moore
neighborhood step. This is the inductive engine of the tight-locality statement
(after one B3/S23 generation, reach expands by exactly one Moore shell), and the
reason the tight Chebyshev reach grows linearly with `t` rather than as `2*t`.
-/

/-- Triangle inequality for the Chebyshev distance. -/
theorem chebDist_triangle (p q r : Int × Int) :
    chebDist p q ≤ chebDist p r + chebDist r q := by
  unfold chebDist
  omega

/-- The Chebyshev cone grows by exactly one Moore step: `q` is within Chebyshev
    radius `t+1` of `p` iff there is a cell `r` within Chebyshev radius `t` of `p`
    that is a Moore neighbor of `q` (Chebyshev radius `≤ 1`). Forward direction
    steps from `q` toward `p` by one unit in each nonzero coordinate; backward
    direction is the triangle inequality. This is the additive-growth lemma that
    underpins the tight `t`-step locality (one Moore shell per generation). -/
theorem chebDist_le_succ_iff (p q : Int × Int) (t : Nat) :
    chebDist p q ≤ t + 1 ↔
      ∃ r : Int × Int, chebDist p r ≤ t ∧ chebDist r q ≤ 1 := by
  constructor
  · -- forward: step from `q` toward `p` by one unit in each nonzero coordinate
    intro h
    unfold chebDist at h
    refine ⟨(q.1 - if q.1 - p.1 = 0 then 0 else if 0 < q.1 - p.1 then 1 else -1,
             q.2 - if q.2 - p.2 = 0 then 0 else if 0 < q.2 - p.2 then 1 else -1), ?_, ?_⟩
    all_goals unfold chebDist; omega
  · -- backward: triangle inequality
    rintro ⟨r, hr, hq⟩
    exact (chebDist_triangle p q r).trans (add_le_add hr hq)

/-- The tight Chebyshev cone is nested in its successor: radius `t` ⊆ radius
    `t+1`. Corollary of `chebDist_le_succ_iff` (or directly `Nat.le_succ`). -/
theorem chebDist_le_succ (p q : Int × Int) (t : Nat) (h : chebDist p q ≤ t) :
    chebDist p q ≤ t + 1 := h.trans (Nat.le_succ t)

end Life
end Conway
