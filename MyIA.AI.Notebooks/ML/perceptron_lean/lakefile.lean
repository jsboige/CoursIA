import Lake
open Lake DSL

/-!
# Mini-projet Lean pédagogique : convergence du Perceptron (théorème de Novikoff)

Projet Lean 4 (avec Mathlib) prouvant le **théorème de convergence du Perceptron**
(Novikoff, 1962) : pour un ensemble de données linéairement séparables de marge γ et
de rayon R, l'algorithme du perceptron effectue au plus `(R/γ)²` mises à jour (erreurs
de classification) avant de converger. Voir l'issue #4051 (roadmap Lean #4038).

Premier théorème Lean de la série **ML**. La preuve est **géométrique élémentaire** :
- l'alignement du vecteur de poids `w` sur le séparateur `u` croît d'au moins `γ` à
  chaque erreur (`⟨w k, u⟩ ≥ k·γ`),
- la norme `‖w k‖²` croît d'au plus `R²` à chaque erreur (`‖w k‖² ≤ k·R²`),
- l'inégalité de Cauchy–Schwarz combine les deux : `k·γ ≤ ‖w k‖·‖u‖ ≤ √k·R`,
  d'où `k ≤ (R/γ)²`.

Mathlib fournit `InnerProductSpace`, Cauchy–Schwarz (`abs_inner_le_norm`) et tout le
calcul d'espace préhilbertien réel nécessaires, sur lesquels la borne se déduit en
quelques lemmes.

Modèle : on se place dans un espace préhilbertien réel abstrait `V` (Novikoff est
indépendant de la dimension) ; les données sont une suite finie de points `ℕ → V`
d'étiquettes `±1`, un séparateur unitaire `u` de marge `γ`, un rayon `R`.

Notebook compagnon (série `ML/ML.Net`) : présentation pédagogique de la
classification linéaire / perceptron. Le câblage du notebook revient au propriétaire
de la série ML (convention des lakes frères : le lake est le livrable formel, le
`lake build` est la preuve d'exécution).
-/

package «perceptron_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

@[default_target]
lean_lib «Perceptron» where
  globs := #[.submodules `Perceptron]
