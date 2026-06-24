import Mathlib
import Minimax.ZeroSum

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

## Milestone suivant (OPEN — documenté, non sorry-stubbé)

Le câblage explicite de `Sion.exists_isSaddlePointOn'` sur `stdSimplex ℝ m ×
stdSimplex ℝ n` (compacité/convexité des simplexes + dérivation des
quasi-convexité/quasi-concavité depuis l'affinité + LSC/USC depuis la continuité) est
le **milestone ouvert** de l'issue #4054 : il n'est **pas** comblé par `sorry` mais
laissé comme étape de formalisation à venir, honnêtement signalé.
-/

namespace MinimaxLean

/-- Statut : `Minimax/ZeroSum.lean` entièrement 0-sorry. Bilinéarité + continuité du
payoff prouvées. L'application finale de Sion sur les simplexes est le milestone OPEN. -/
abbrev Status : Prop := True

end MinimaxLean
