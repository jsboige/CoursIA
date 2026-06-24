import Lake
open Lake DSL

/-!
# Mini-projet Lean pédagogique : admissibilité de la relaxation sans-delete (h⁺)

Projet Lean 4 (avec Mathlib) prouvant l'**admissibilité de la relaxation sans-delete**
en planification STRIPS : la relaxation ignore les effets de *deletion* (`del`) des
actions, ce qui rend l'atteignabilité **monotone** (l'état ne fait que grandir). Le
résultat fondamental est

    h⁺ ≤ h*

où `h⁺` (resp. `h*`) est le coût du plan relaxé optimal (resp. plan réel optimal) :
**tout plan réel est un plan relaxé**, donc le minimum sur les plans relaxés est
inférieur au minimum sur les plans réels. Cette admissibilité justifie formellement
les heuristiques de relaxation FF / h_add / h_max au cœur du planning classique.

Voir l'issue #4053 (roadmap Lean #4038, Tier 2).

**Faisabilité** : combinatoire élémentaire sur les `Finset`. Le lemme clé est
`step a s ⊆ stepR a s` (car `s \ a.del ⊆ s`), remonté aux séquences d'actions par
induction sur la longueur du plan via la monotonie de l'exécution. Aucune infra dédiée
requise dans Mathlib. Le théorème phare `relaxed_plan_admissible` est atteignable
**0 sorry**.

Notebook compagnon (série `Planners`) : présentation pédagogique des heuristiques de
relaxation (h_max, h_add, FF). Conventions des lakes frères : le lake est le livrable
formel, le `lake build` est la preuve d'exécution ; le câblage du notebook compagnon
revient au propriétaire de la série Planners.
-/

package «planning_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

@[default_target]
lean_lib «Planning» where
  globs := #[.submodules `Planning]
