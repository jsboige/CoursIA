import Lake
open Lake DSL

/-!
# Mini-projet Lean pédagogique : critère de Kelly (optimalité du log-croissance)

Projet Lean 4 (avec Mathlib) prouvant l'**optimalité du critère de Kelly** pour le
position sizing : pour un pari de Bernoulli (probabilité `p` de gagner, cote nette
`b`), la fraction optimale du capital à risquer est

    f* = (b·p − q) / b        (q = 1 − p)

qui **maximise de façon unique** le taux de croissance espéré `g(f) = p·log(1 + b·f)
+ q·log(1 − f)`. Les sur-paris (`f > f*`) et sous-paris (`f < f*`) sont strictement
sous-optimaux. Voir l'issue #4052 (roadmap Lean #4038, Tier 2).

**Pourquoi ici** : le Kelly criterion fonde le **position sizing** (au cœur du trading
enseigné dans la série QuantConnect), et relie la série trading à un résultat
mathématique propre et démontrable.

**Faisabilité** : `Real.log` est strictement concave sur `(0, ∞)` (`StrictConcaveOn`
dans Mathlib) ; `g(f)` est strictement concave comme combinaison convexe de
compositions affines strictement concaves. La condition du premier ordre `g'(f*) = 0`
+ la stricte concavité ⟹ `f*` est l'**unique maximiseur**. Calcul réel standard,
atteignable **0 sorry** sur le théorème phare `kelly_optimal`.

Notebook compagnon (série `QuantConnect`) : présentation pédagogique du position
sizing / Kelly (Python, paire Lean + Python côte à côte). Le câblage du notebook
revient au propriétaire de la série QuantConnect (convention des lakes frères : le
lake est le livrable formel, le `lake build` est la preuve d'exécution).
-/

package «kelly_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

@[default_target]
lean_lib «Kelly» where
  globs := #[.submodules `Kelly]
