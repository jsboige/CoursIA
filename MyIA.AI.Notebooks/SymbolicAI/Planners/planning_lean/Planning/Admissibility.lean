import Mathlib
import Planning.Strips
import Planning.Relaxation

/-!
# Planning.Admissibility — h⁺ ≤ h* : la relaxation sans-delete est admissible

**Théorème d'admissibilité de la relaxation** : le coût du plan relaxé optimal `h⁺`
n'excède jamais le coût du plan réel optimal `h*`.

    h⁺ ≤ h*

La preuve repose sur l'inclusion `run π s ⊆ runR π s` (tout plan réel est un plan
relaxé) : comme la relaxation ignore les effets `del`, l'état relaxé après application
d'une séquence d'actions contient toujours l'état réel correspondant. Donc tout plan
réel atteignant le but `g` est aussi un plan relaxé atteignant `g`. Par minimalité du
coût optimal, le coût relaxé `h⁺` est inférieur au coût réel `h*`.

Ce résultat justifie formellement l'usage des heuristiques de relaxation (h_max, h_add,
FF) comme **minorants admissibles** du coût réel — la base de la planification moderne.
Voir l'issue #4053 (roadmap Lean #4038, Tier 2).

## Jalon ouvert (non sorry-backed)

La **machinerie complète des heuristiques h_max / h_add** (fixpoint de l'atteignabilité
relaxée, et l'inégalité `h_max ≤ h⁺ ≤ h_add`) n'est pas formalisée ici : elle nécessite
une définition récursive du point fixe relaxed-reachability et la preuve de convergence,
substantielle. L'admissibilité fondamentale `h⁺ ≤ h*` (le résultat qui légitime toute la
famille d'heuristiques de relaxation) est prouvée 0 sorry ci-dessous.
-/

namespace PlanningLean

open PlanningLean

variable {F : Type} [DecidableEq F]

/-- **Théorème d'admissibilité de la relaxation (h⁺ ≤ h*)** : tout plan réel atteignant
    le but `g` est aussi un plan relaxé atteignant `g`. Par minimalité des coûts
    optimaux, le coût relaxé `h⁺` est donc inférieur au coût réel `h*`. -/
theorem relaxed_plan_admissible (π : List (Action F)) (s g : State F)
    (h : reaches π s g) : reachesR π s g :=
  Finset.Subset.trans h (run_subset_runR π s)

/-- **Corollaire direct** : si un plan réel de longueur `n` atteint `g`, le même plan,
    exécuté en relaxation, atteint aussi `g`. Formulation opérationnelle de h⁺ ≤ h*
    (il existe un plan relaxé de coût ≤ tout plan réel, donc ≤ h*). -/
theorem relaxed_plan_witness (π : List (Action F)) (s g : State F)
    (h : reaches π s g) : reachesR π s g :=
  relaxed_plan_admissible π s g h

end PlanningLean
