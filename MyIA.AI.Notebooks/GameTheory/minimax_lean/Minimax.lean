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
-/

namespace MinimaxLean

/-- Statut : le théorème minimax de von Neumann (forme point-selle) est **prouvé 0-sorry**
via `Minimax/SionApplication.lean`. Milestone #4054 RÉSOLU. -/
abbrev Status : Prop := True

end MinimaxLean
