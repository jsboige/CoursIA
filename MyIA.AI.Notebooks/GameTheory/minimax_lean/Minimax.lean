import Mathlib
import Minimax.ZeroSum
import Minimax.Concavity

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

## Milestone suivant (OPEN — documenté, non sorry-stubbé)

Les **4 hyps analytiques** de `Sion.exists_isSaddlePointOn'` (quasi-convexité en `x`,
quasi-concavité en `y`, semi-continuité inférieure en `x`, supérieure en `y`) sont
désormais **prouvées 0 sorry** dans `Concavity.lean`. Reste le **milestone ouvert** de
l'issue #4054 : les instances topologiques `Pi`-sur-`ℝ`, la non-vacuité des simplexes
(`stdSimplex`, faits Mathlib), et l'**application finale** réunissant les 4 hyps avec
`isCompact_stdSimplex`/`convex_stdSimplex` vers `Sion.exists_isSaddlePointOn'`. Non
comblé par `sorry`, laissé comme étape de formalisation à venir, honnêtement signalé.
-/

namespace MinimaxLean

/-- Statut : `Minimax/ZeroSum.lean` + `Concavity.lean` entièrement 0-sorry. Bilinéarité
+ continuité du payoff, et les 4 hyps analytiques de Sion prouvées. Reste le câblage
topologique final (instances Pi/ℝ + non-vacuité + application `Sion.minimax'`). -/
abbrev Status : Prop := True

end MinimaxLean
