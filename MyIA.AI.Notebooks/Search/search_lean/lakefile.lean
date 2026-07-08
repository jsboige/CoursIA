import Lake
open Lake DSL

/-!
# Mini-projet Lean pédagogique : optimalité de A*

Projet Lean 4 (avec Mathlib) formalisant le **théorème phare d'optimalité de A*** :
une heuristique **admissible** garantit que A* renvoie un chemin de coût optimal
(Hart, Nilsson & Raphael, 1968). Voir l'issue #4048 (roadmap #4038) et le registre
#3801 (prong B « problème non-trivial » — répond au grief « BFS vs A* dégénéré »
sur graphe à coût uniforme, où l'heuristique ne discrimine pas).

Approche : **lemme d'optimalité abstrait** (sans modéliser la file de priorité
complète), comme suggéré par #4048. Modèle : graphe pondéré à arêtes non-négatives
(`NNReal`), chemins comme listes de sommets, heuristique admissible/consistante,
`hStar` = « vrai coût optimal restant » (borne inférieure sur le coût des chemins
menant au but).

Notebooks compagnons (`Search-2-Uninformed.ipynb` + `Search-3-Informed.ipynb`,
série Search, sous-série Part1-Foundations) : présentation pédagogique +
contre-exemple BFS-vs-A* sur graphe pondéré. Le notebook historique
`Exploration_non_informée_et_informée_intro.ipynb` (autrefois à la racine Search,
archivé en 2026-07-03 dans `archive/`) couvrait le même contenu en un document
unique. Le câblage du notebook revient au propriétaire de la série Search.
-/

package «search_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

@[default_target]
lean_lib «Astar» where
  globs := #[.submodules `Astar]
