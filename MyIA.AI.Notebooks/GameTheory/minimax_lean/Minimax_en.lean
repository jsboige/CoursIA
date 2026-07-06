import Mathlib
import Minimax.ZeroSum_en
import Minimax.Concavity_en
import Minimax.SionApplication_en

/-!
# minimax_lean — bilinearity of the payoff for von Neumann's minimax theorem

English mirror of `Minimax.lean` (FR-first canonical), EPIC #4980 (i18n Lean).
Convention ratified by ai-01 (2026-07-04, #4980 comment-4881909354): distinct FR +
EN sibling files in the same lake, both compile; namespace `MinimaxLean_en`
(anti-collision with FR `MinimaxLean`); non-docstring content byte-identical
(CI drift-detectable); EN docstrings manually translated.

Lean 4 lake (Mathlib) at the root of the **zero-sum** specialisation of the
`GameTheory` series, formalising the analytical core of **von Neumann's minimax
theorem** for finite zero-sum games:

    maxₓ minᵧ xᵀ A y = minᵧ maxₓ xᵀ A y

(`x` ranges over the mixed-strategy simplex of the row player, `y` over that of
the column player). See issue #4054 (Lean roadmap #4038).

## Formalisation strategy (from Mathlib `Topology.Sion`)

The full theorem follows from **Sion's minimax** (`Sion.exists_isSaddlePointOn'`),
whose bilinear case on compact convex simplexes yields exactly von Neumann. The
Sion hypotheses for `f = payoff A` on `X = stdSimplex ℝ m`, `Y = stdSimplex ℝ n`
are:
- `IsCompact`/`Convex`/`Nonempty` of the simplexes (Mathlib facts on `stdSimplex`);
- `UpperSemicontinuousOn`/`LowerSemicontinuousOn` — since `payoff` is **continuous**;
- `QuasiconcaveOn`/`QuasiconvexOn` — since `payoff` is **affine in each variable**.

This first deliverable establishes the **formal core**: the bilinearity of the
payoff, which carries these four hypotheses.

- `Minimax/ZeroSum_en.lean` — payoff matrix, bilinear payoff `xᵀ A y = Σᵢⱼ xᵢ Aᵢⱼ yⱼ`,
  additivity + homogeneity in each variable (`payoff_add_in_x`, `payoff_smul_in_x`,
  `payoff_add_in_y`, `payoff_smul_in_y`), joint and restricted continuity
  (`continuous_payoff`, `continuous_payoff_in_x`, `continuous_payoff_in_y`). **0 sorry.**
- `Minimax/Concavity_en.lean` — **Sion glue (iterations 1 & 2)**: concavity/convexity
  of the payoff on the simplexes (`payoff_concave_in_x`, `payoff_convex_in_x`, and in
  `y`), then quasi-concavity/quasi-convexity via Mathlib bridges
  (`payoff_quasiconcave_in_y`, `payoff_quasiconvex_in_x`) — iteration 1: 2 of the 4
  analytical hyps of `Sion.exists_isSaddlePointOn'`. **Iteration 2**: semi-continuity
  derived from continuity (`payoff_lowerSemicontinuous_in_x`,
  `payoff_upperSemicontinuous_in_y`) — the **remaining 2 hyps**.
  **All 4 analytical hyps are now proved. 0 sorry.**
- `Minimax/SionApplication_en.lean` — **iteration 3 of the Sion glue**: non-emptiness
  of the simplexes (`stdSimplex_nonempty_m/n` via `single_mem_stdSimplex`) then the
  **final application** `exists_saddle_point_payoff` — von Neumann's theorem
  (saddle-point form) proved in a single application of `Sion.exists_isSaddlePointOn`
  gathering the 4 analytical hyps + compactness `isCompact_stdSimplex` + convexity
  `convex_stdSimplex` + non-emptiness. The `Pi`-over-`ℝ` topological instances
  (`TopologicalSpace`, `AddCommGroup`, `Module ℝ`, `IsTopologicalAddGroup`,
  `ContinuousSMul ℝ`) synthesise from Mathlib. **Milestone #4054 RESOLVED. 0 sorry.**

## Milestone — RESOLVED (#4054)

Von Neumann's **minimax theorem** (saddle-point form) is now **proved 0-sorry** via
`Minimax/SionApplication_en.lean` (`exists_saddle_point_payoff`): for any payoff matrix
`A` over non-empty finite types, there exist `a ∈ Δₘ`, `b ∈ Δₙ` such that
`payoff A a y ≤ payoff A x b` for all `x ∈ Δₘ`, `y ∈ Δₙ`. Proved in a single
application of `Sion.exists_isSaddlePointOn` (real case, `Topology/Sion.lean`),
gathering the 4 analytical hyps of `Concavity_en.lean` (quasi-convexity in `x`,
quasi-concavity in `y`, lower semi-continuity in `x`, upper in `y`) with the
compactness/convexity/non-emptiness of the simplexes (Mathlib facts
`isCompact_stdSimplex`/`convex_stdSimplex`/`single_mem_stdSimplex`).
-/

namespace MinimaxLean_en

/-- Status: von Neumann's minimax theorem (saddle-point form) is **proved 0-sorry**
via `Minimax/SionApplication_en.lean`. Milestone #4054 RESOLVED. -/
abbrev Status : Prop := True

end MinimaxLean_en
