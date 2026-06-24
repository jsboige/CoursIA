import Lake
open Lake DSL

/-!
# Mini-projet Lean pédagogique : théorème minimax de von Neumann (jeux à somme nulle)

Projet Lean 4 (avec Mathlib) prouvant le **théorème minimax de von Neumann** pour les
jeux finis à somme nulle : pour toute matrice de gains `A` (m × n), les stratégies
mixtes optimales existent et la valeur du jeu vérifie

    maxₓ minᵧ xᵀ A y = minᵧ maxₓ xᵀ A y

(`x` parcourt le simplexe des stratégies mixtes du joueur-ligne, `y` celui du
joueur-colonne). Voir l'issue #4054 (roadmap Lean #4038).

Le théorème suit du **minimax de Sion** (Mathlib `Topology.Sion`), dont le cas bilinéaire
sur des simplexes compacts convexes redonne exactement von Neumann : le payoff
`xᵀ A y` est **affine en chaque variable**, donc (i) continu ⟹ semi-continu
supérieurement et inférieurement, (ii) affine ⟹ quasi-convexe et quasi-concave — les
quatre hypothèses de `Sion.exists_isSaddlePointOn'`.

**Faisabilité réévaluée** : l'issue #4054 classait ce théorème « MOYENNE-DURE » en
supposant qu'il faudrait prouver Sion/Kakutani à la main. Mathlib `v4.31.0-rc1` fournit
`Sion.exists_isSaddlePointOn'` + `stdSimplex` (compact convexe) : le théorème complet est
donc atteignable **0 sorry**, le travail étant de câbler la bilinéarité/convexité du
payoff sur les simplexes — honnêtement documenté comme le cœur de la formalisation.

Notebook compagnon (série `GameTheory`) : présentation pédagogique des jeux à somme
nulle. Le câblage du notebook revient au propriétaire de la série GameTheory
(convention des lakes frères : le lake est le livrable formel, le `lake build` est la
preuve d'exécution).
-/

package «minimax_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

@[default_target]
lean_lib «Minimax» where
  globs := #[.submodules `Minimax]
