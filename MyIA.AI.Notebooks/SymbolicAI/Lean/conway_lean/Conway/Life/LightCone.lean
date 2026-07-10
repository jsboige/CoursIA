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

end Life
end Conway
