import Mathlib
import Minimax.ZeroSum_en
import Minimax.Concavity_en

/-!
  Minimax.SionApplication — final Sion application (Sion glue iteration 3)
  ========================================================================

  English mirror of `Minimax/SionApplication.lean` (FR-first canonical).
  Convention i18n Lean ratifiée par ai-01 (2026-07-04, #4980 comment-4881909354) :
  fichiers `.lean` distincts FR + EN siblings dans le même lake, les deux compilent.
  Drift-CI detectable : contenu non-docstring byte-identique entre siblings.

  Note méthodologique : traduction manuelle du FR canonique (pas de source
  EN historique pré-Option A à recover, fichier FR-first depuis origin).

  This module wires the **4 analytic hypotheses** proved in `Concavity.lean`
  (quasi-convexity in `x`, quasi-concavity in `y`, lower semicontinuity in
  `x`, upper in `y`) with Mathlib's topological facts on `stdSimplex`
  (compactness `isCompact_stdSimplex`, convexity `convex_stdSimplex`,
  non-vacuity via `single_mem_stdSimplex`) to prove the existence of a
  saddle point via `Sion.exists_isSaddlePointOn` (real case) — the
  **final milestone** of #4054.

  The 5 topological prerequisites of Sion on `E = m → ℝ` (and `F = n → ℝ`)
  are `TopologicalSpace`, `AddCommGroup`, `Module ℝ`,
  `IsTopologicalAddGroup`, `ContinuousSMul ℝ`: they are synthesized from
  the `Pi` instances of Mathlib (`Pi.topologicalSpace`,
  `Pi.instAddCommGroup`, `Pi.instModule`, etc.). This **iteration 3**
  module delivers the auxiliary fact of **non-vacuity of the simplex**
  and then the **final application**.

  `IsSaddlePointOn` lives at top level
  (`Mathlib/Order/SaddlePoint.lean`), while `exists_isSaddlePointOn`
  is in `namespace Sion`.
-/

namespace MinimaxLean_en

open Set

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [Nonempty m] [Nonempty n]
variable (A : PayoffMatrix m n)

/-- The standard simplex `stdSimplex ℝ m` is non-empty as soon as `m`
is non-empty: the Dirac `Pi.single i 1` (mass 1 on index `i`, zero
elsewhere) is a point of the simplex, via the Mathlib lemma
`single_mem_stdSimplex`. -/
lemma stdSimplex_nonempty_m : (stdSimplex ℝ m).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty m›
  exact ⟨Pi.single i 1, single_mem_stdSimplex (𝕜 := ℝ) i⟩

/-- Variant in `y`: `stdSimplex ℝ n` is non-empty as soon as `n` is
non-empty. -/
lemma stdSimplex_nonempty_n : (stdSimplex ℝ n).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty n›
  exact ⟨Pi.single i 1, single_mem_stdSimplex (𝕜 := ℝ) i⟩

/-- **Von Neumann's minimax theorem (saddle-point form)** — the
**final milestone** of issue #4054: for every payoff matrix `A` on
finite non-empty types, there exist mixed strategies `a ∈ Δₘ`,
`b ∈ Δₙ` such that `payoff A a y ≤ payoff A x b` for all `x ∈ Δₘ`,
`y ∈ Δₙ` (saddle point). Proved by a single application of
`Sion.exists_isSaddlePointOn` (real case, `Topology/Sion.lean` section
`Real`), gathering:
- compactness: `isCompact_stdSimplex ℝ`;
- convexity: `convex_stdSimplex ℝ`;
- non-vacuity: `stdSimplex_nonempty_m` / `stdSimplex_nonempty_n`
  (lemmas above);
- the 4 analytic hypotheses of `Concavity.lean` (quasi-convexity in
  `x`, quasi-concavity in `y`, lower semicontinuity in `x`, upper in
  `y`).

The 5 topological prerequisites of Sion on `E = m → ℝ` and
`F = n → ℝ` (`TopologicalSpace`, `AddCommGroup`, `Module ℝ`,
`IsTopologicalAddGroup`, `ContinuousSMul ℝ`) are synthesized from the
Mathlib `Pi` instances. -/
theorem exists_saddle_point_payoff :
    ∃ a ∈ stdSimplex ℝ m, ∃ b ∈ stdSimplex ℝ n,
      IsSaddlePointOn (stdSimplex ℝ m) (stdSimplex ℝ n) (payoff A) a b :=
  Sion.exists_isSaddlePointOn
    (ne_X := stdSimplex_nonempty_m)
    (cX := convex_stdSimplex ℝ m)
    (kX := isCompact_stdSimplex (𝕜 := ℝ) (ι := m))
    (hfy := fun y _hy => payoff_lowerSemicontinuous_in_x A y)
    (hfy' := fun y _hy => payoff_quasiconvex_in_x A y)
    (cY := convex_stdSimplex ℝ n)
    (ne_Y := stdSimplex_nonempty_n)
    (kY := isCompact_stdSimplex (𝕜 := ℝ) (ι := n))
    (hfx := fun x _hx => payoff_upperSemicontinuous_in_y A x)
    (hfx' := fun x _hx => payoff_quasiconcave_in_y A x)

end MinimaxLean_en
