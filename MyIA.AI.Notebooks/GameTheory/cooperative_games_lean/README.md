# Jeux coopératifs — Lean 4

Formalisation en Lean 4 de la théorie des jeux coopératifs : **valeur de Shapley** (caractérisation axiomatique de Shapley 1953, unicité via décomposition de Möbius) et **théorème de Bondareva-Shapley** caractérisant le Cœur des jeux coopératifs par l'équilibrage.

> Version anglaise préservée dans [`README.en.md`](README.en.md).

## Statut

- **Toolchain** : `leanprover/lean4:v4.30.0-rc2`
- **Compte de sorry** : **0** (aucun `sorry` comme tactique sur l'ensemble du projet)
- **Build** : `lake build CooperativeGames` — SUCCESS
- **Dépendances** : Mathlib4 (épinglée via `lake-manifest.json`)
- **Certification** : **COMPLETE** — tous les théorèmes annoncés sont prouvés sans axiome ajouté

## Modules

| Fichier | Lignes | sorry | Description |
|---------|--------|-------|-------------|
| `CooperativeGames/Shapley.lean` | 1042 | 0 | Valeur de Shapley, caractérisation axiomatique (efficacité, symétrie, joueur nul, additivité), unicité via décomposition de Möbius |
| `CooperativeGames/Basic.lean` | 594 | 0 | Jeu coopératif (TU), fonction caractéristique, Cœur, jeux équilibrés, théorème de Bondareva-Shapley, jeux convexes |
| `CooperativeGames/ConeKernel.lean` | 733 | 0 | Mécanique de séparation par cône (cône d'incidence augmenté, fermeture, caractérisation duale) pour la direction backward de Bondareva-Shapley |

## Résultats clés

- **Caractérisation de Shapley** (`Shapley.lean`) : la valeur de Shapley est l'allocation *unique* satisfaisant les quatre axiomes (efficacité, symétrie, joueur nul, additivité) — Shapley (1953). L'unicité passe par la décomposition de Möbius (`mobius_decomposition`, PR #1024). 0 sorry.
- **Théorème de Bondareva-Shapley** (`Basic.lean`, L434) :
  ```lean
  theorem bondareva_shapley : G.Core.Nonempty ↔ G.Balanced
  ```
  Bi-implication **entièrement prouvée**, 0 sorry. Bondareva (1963) / Shapley (1967).
- **Cœur des jeux convexes non vide** (`Basic.lean`, L588) :
  ```lean
  theorem convex_core_nonempty (h : G.Convex) : G.Core.Nonempty
  ```
  Via les vecteurs marginaux (Shapley 1971), `marginalVector_mem_core`.

### Comment la direction backward a été close

La direction `Balanced → Cœur non vide` (`bondareva_shapley_backward`) est le sens difficile. Elle se décompose en :

1. **Mécanique de cône** (`ConeKernel.lean`) : on encode les poids équilibrés dans le cône d'incidence augmenté `augCone ⊆ (Option N) → ℝ`, on prouve sa fermeture (`finGenCone_isClosed`, `conicHull_linearIndependent_isClosed`) et sa caractérisation duale (`augCone_dual_iff`). La condition équilibrée force le point « d'unité équilibrée » `balancedUnit` hors de ce cône, d'où par séparation un fonctionnel linéaire séparateur.
2. **Décodage** (`Basic.lean`) : le fonctionnel séparateur se traduit en une allocation du Cœur (`exists_preimputation_strict_core`, cf #3945).
3. **Noyau d'atteinte `hb_witness`** (`Basic.lean`, L348) : existence d'une allocation `x ∈ P` avec `∑ xᵢ ≤ v(N)`. Clos par un argument de **tranche compacte + Weierstrass** : la tranche de sous-niveau `S₁ = {x ∈ P | ∑x ≤ v(N)+1}` est un fermé inclus dans la boîte compacte `∏ᵢ Icc (v({i})) (v(N)+1 − v(N∖{i}))`, donc compacte ; la fonctionnelle continue `∑x` y atteint son minimum, et une ε-contradiction contre `hb_strict` force ce minimum à valoir `≤ v(N)` (PR #3954).

Cette dernière étape était le seul `sorry` restant (`hb_witness`), longtemps taggé `INTRACTABLE_UNTIL_BONDAREVA_HYPERPLANE_SEPARATION` faute d'un lemme de séparation adapté dans Mathlib ; la voie de passage retenue (séparation sur le cône fini + attainment par compacité) contourne ce lemme manquant **sans axiome ajouté**.

## Notes

- Lié à [`stable_marriage_lean/`](../stable_marriage_lean/) (appariement Gale-Shapley) et [`social_choice_lean/`](../social_choice_lean/) (Arrow / Sen).
- Le plan historique de séparation de Farkas [`docs/BONDAREVA_FARKAS_PLAN.md`](docs/BONDAREVA_FARKAS_PLAN.md) (2026-06-20) est **supersédé** par la résolution effective (compact-slice Weierstrass, #3954) ; conservé pour la traçabilité.
- État formel détaillé : [`FORMAL_STATUS.md`](FORMAL_STATUS.md). Inventaire croisé Lean : [`../LEAN_INVENTORY.md`](../LEAN_INVENTORY.md).

## Pour aller plus loin

- **Théorie** : Shapley (1953), *A Value for n-Person Games* ; Bondareva (1963) ; Shapley (1967), *On Balanced Sets and Cores* ; Shapley (1971), *Cores of Convex Games*.
- **Extensions possibles** : indice de pouvoir de Banzhaf (définitions `BanzhafRaw`/`Critical` présentes, théorèmes à écrire), propriétés calculatoires de la valeur de Shapley.
