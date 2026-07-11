import Mathlib
import Minimax.ZeroSum
import Minimax.Concavity
import Minimax.SionApplication

/-!
# minimax_lean — bilinéarité du payoff pour le théorème minimax de von Neumann

Lake Lean 4 (Mathlib) à la racine de la spécialisation **somme nulle** de la série
`GameTheory`, formalisant le socle analytique du **théorème minimax de von Neumann**
pour les jeux finis à somme nulle :

    maxₓ minᵧ xᵀ A y = minᵧ maxₓ xᵀ A y

(`x` parcourt le simplexe des stratégies mixtes du joueur-ligne, `y` celui du
joueur-colonne). Voir l'issue #4054 (roadmap Lean #4038).

## Stratégie de formalisation (depuis Mathlib `Topology.Sion`)

Le théorème complet suit du **minimax de Sion** (`Sion.exists_isSaddlePointOn'`),
dont le cas bilinéaire sur des simplexes compacts convexes redonne exactement von
Neumann. Les hypothèses de Sion pour `f = payoff A` sur `X = stdSimplex ℝ m`,
`Y = stdSimplex ℝ n` sont :
- `IsCompact`/`Convex`/`Nonempty` des simplexes (faits Mathlib sur `stdSimplex`) ;
- `UpperSemicontinuousOn`/`LowerSemicontinuousOn` — car `payoff` est **continu** ;
- `QuasiconcaveOn`/`QuasiconvexOn` — car `payoff` est **affine en chaque variable**.

Ce premier livrable établit le **cœur formel** : la bilinéarité du payoff, qui porte
ces quatre hypothèses.

- `Minimax/ZeroSum.lean` — matrice de gains, payoff bilinéaire `xᵀ A y = Σᵢⱼ xᵢ Aᵢⱼ yⱼ`,
  additivité + homogénéité en chaque variable (`payoff_add_in_x`, `payoff_smul_in_x`,
  `payoff_add_in_y`, `payoff_smul_in_y`), continuité jointe et restreinte
  (`continuous_payoff`, `continuous_payoff_in_x`, `continuous_payoff_in_y`). **0 sorry.**
- `Minimax/Concavity.lean` — **glue Sion (itérations 1 & 2)** : concavité/cvxicité du
  payoff sur les simplexes (`payoff_concave_in_x`, `payoff_convex_in_x`, et en `y`),
  puis quasi-concavité/quasi-convexité via les ponts Mathlib
  (`payoff_quasiconcave_in_y`, `payoff_quasiconvex_in_x`) — itération 1 : 2 des 4 hyps
  analytiques de `Sion.exists_isSaddlePointOn'`. **Itération 2** : semi-continuité
  dérivée de la continuité (`payoff_lowerSemicontinuous_in_x`,
  `payoff_upperSemicontinuous_in_y`) — les **2 hyps restantes**.
  **Les 4 hyps analytiques sont désormais prouvées. 0 sorry.**
- `Minimax/SionApplication.lean` — **itération 3 du glue Sion** : non-vacuité des
  simplexes (`stdSimplex_nonempty_m/n` via `single_mem_stdSimplex`) puis **application
  finale** `exists_saddle_point_payoff` — le théorème de von Neumann (forme point-selle)
  prouvé en une application de `Sion.exists_isSaddlePointOn` réunissant les 4 hyps
  analytiques + compacité `isCompact_stdSimplex` + convexité `convex_stdSimplex` +
  non-vacuité. Les instances topologiques `Pi`-sur-`ℝ` (`TopologicalSpace`,
  `AddCommGroup`, `Module ℝ`, `IsTopologicalAddGroup`, `ContinuousSMul ℝ`) se
  synthétisent depuis Mathlib. **Milestone #4054 RÉSOLU. 0 sorry.**

## Milestone — RÉSOLU (#4054)

Le théorème minimax de **von Neumann** (forme point-selle) est désormais **prouvé
0-sorry** via `Minimax/SionApplication.lean` (`exists_saddle_point_payoff`) : pour toute
matrice de gains `A` sur des types finis non vides, il existe `a ∈ Δₘ`, `b ∈ Δₙ` tels
que `payoff A a y ≤ payoff A x b` pour tout `x ∈ Δₘ`, `y ∈ Δₙ`. Démontré en une
application de `Sion.exists_isSaddlePointOn` (cas réel, `Topology/Sion.lean`), réunissant
les 4 hyps analytiques de `Concavity.lean` (quasi-convexité en `x`, quasi-concavité en
`y`, semi-continuité inf. en `x`, sup. en `y`) avec la compacité/convexité/non-vacuité
des simplexes (faits Mathlib `isCompact_stdSimplex`/`convex_stdSimplex`/`single_mem_stdSimplex`).

---

# minimax_lean — payoff bilinearity for von Neumann's minimax theorem

Lean 4 (Mathlib) lake at the root of the **zero-sum** specialization of the
`GameTheory` series, formalizing the analytic foundation of **von Neumann's
minimax theorem** for finite zero-sum games:

    maxₓ minᵧ xᵀ A y = minᵧ maxₓ xᵀ A y

(`x` ranges over the row-player's mixed-strategy simplex, `y` over the
column-player's one). See issue #4054 (Lean roadmap #4038).

## Formalization strategy (from Mathlib `Topology.Sion`)

The full theorem follows from **Sion's minimax theorem** (`Sion.exists_isSaddlePointOn'`),
whose bilinear case on compact convex simplices recovers exactly von
Neumann. Sion's hypotheses for `f = payoff A` on `X = stdSimplex ℝ m`,
`Y = stdSimplex ℝ n` are:
- `IsCompact`/`Convex`/`Nonempty` of the simplices (Mathlib facts on `stdSimplex`);
- `UpperSemicontinuousOn`/`LowerSemicontinuousOn` — because `payoff` is **continuous**;
- `QuasiconcaveOn`/`QuasiconvexOn` — because `payoff` is **affine in each variable**.

This first deliverable establishes the **formal core**: payoff bilinearity, which
carries these four hypotheses.

- `Minimax/ZeroSum.lean` — payoff matrix, bilinear payoff `xᵀ A y = Σᵢⱼ xᵢ Aᵢⱼ yⱼ`,
  additivity + homogeneity in each variable (`payoff_add_in_x`, `payoff_smul_in_x`,
  `payoff_add_in_y`, `payoff_smul_in_y`), joint and restricted continuity
  (`continuous_payoff`, `continuous_payoff_in_x`, `continuous_payoff_in_y`). **0 sorry.**
- `Minimax/Concavity.lean` — **Sion glue (iterations 1 & 2)**: concavity/convexity of the
  payoff on the simplices (`payoff_concave_in_x`, `payoff_convex_in_x`, and in `y`),
  then quasiconcavity/quasiconvexity via the Mathlib bridges
  (`payoff_quasiconcave_in_y`, `payoff_quasiconvex_in_x`) — iteration 1: 2 of the 4
  analytic hyps of `Sion.exists_isSaddlePointOn'`. **Iteration 2**: semicontinuity
  derived from continuity (`payoff_lowerSemicontinuous_in_x`,
  `payoff_upperSemicontinuous_in_y`) — the **2 remaining hyps**.
  **The 4 analytic hyps are now proven. 0 sorry.**
- `Minimax/SionApplication.lean` — **iteration 3 of the Sion glue**: non-emptiness of
  the simplices (`stdSimplex_nonempty_m/n` via `single_mem_stdSimplex`) then **final
  application** `exists_saddle_point_payoff` — von Neumann's theorem (saddle-point form)
  proven in one application of `Sion.exists_isSaddlePointOn` gathering the 4 analytic
  hyps + compactness `isCompact_stdSimplex` + convexity `convex_stdSimplex` +
  non-emptiness. The topological `Pi`-over-`ℝ` instances (`TopologicalSpace`,
  `AddCommGroup`, `Module ℝ`, `IsTopologicalAddGroup`, `ContinuousSMul ℝ`) are
  synthesized from Mathlib. **Milestone #4054 RESOLVED. 0 sorry.**

## Milestone — RESOLVED (#4054)

**von Neumann's** minimax theorem (saddle-point form) is now **proven 0-sorry**
via `Minimax/SionApplication.lean` (`exists_saddle_point_payoff`): for any
payoff matrix `A` over non-empty finite types, there exist `a ∈ Δₘ`, `b ∈ Δₙ` such
that `payoff A a y ≤ payoff A x b` for all `x ∈ Δₘ`, `y ∈ Δₙ`. Demonstrated in one
application of `Sion.exists_isSaddlePointOn` (real case, `Topology/Sion.lean`),
gathering the 4 analytic hyps from `Concavity.lean` (quasiconvexity in `x`,
quasiconcavity in `y`, lower semicontinuity in `x`, upper in `y`) with
compactness/convexity/non-emptiness of the simplices (Mathlib facts
`isCompact_stdSimplex`/`convex_stdSimplex`/`single_mem_stdSimplex`).

Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier root
aggregator est bilingue inline (FR canonique d'abord, EN en miroir),
conformément au pattern canonique `CooperativeGames.lean` (pilote EPIC #4980,
PR #5883 MERGED 2026-07-10) et `RepeatedGames.lean` (c.356, PR #6048 MERGED
2026-07-11). Les modules substantiels (`Minimax.ZeroSum`, `Minimax.Concavity`,
`Minimax.SionApplication`) vivent dans des fichiers siblings `_en.lean`
séparés lorsque pertinent (cf. #4980 Phase 0.5, décision user ratifiée
2026-07-04 sur la paire FR-canonical-first + EN-mirror-second).
-/

namespace MinimaxLean

/-- Statut : le théorème minimax de von Neumann (forme point-selle) est **prouvé 0-sorry**
via `Minimax/SionApplication.lean`. Milestone #4054 RÉSOLU. -/
abbrev Status : Prop := True

end MinimaxLean
