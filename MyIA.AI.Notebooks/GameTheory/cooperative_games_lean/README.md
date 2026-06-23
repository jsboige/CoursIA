# Cooperative Games Lean

Formalisation en Lean 4 de la théorie des jeux coopératifs (valeur de Shapley, cœur).

## Statut

- **Toolchain** : v4.30.0-rc2
- **Compte de sorry** : **0** — le théorème de Bondareva-Shapley est prouvé dans les deux directions
- **Build** : `lake build CooperativeGames` — SUCCESS
- **Dépendances** : Mathlib4

## Modules

| Fichier | sorry | Description |
|---------|-------|-------------|
| `CooperativeGames/Shapley.lean` | 0 | Définition de la valeur de Shapley et théorème d'unicité |
| `CooperativeGames/Basic.lean` | 0 | Jeu coopératif / fonction caractéristique / Cœur / théorème de Bondareva-Shapley |
| `CooperativeGames/ConeKernel.lean` | 0 | Noyau Farkas / séparation de cône (machinerie prouvant la direction backward) |

## Résultats clés

- **Unicité de la valeur de Shapley** : prouvé que la valeur de Shapley est l'unique valeur satisfaisant les axiomes d'efficacité, symétrie, joueur nul et additivité (Shapley.lean, 0 sorry)
- **Définitions du Cœur** : jeu coopératif, fonction caractéristique, ensemble des joueurs, Cœur (Basic.lean)
- **Direction `←` de Bondareva-Shapley** (balanced ⇒ Cœur non vide) : **entièrement prouvée** via la machinerie de séparation de cône du module `ConeKernel.lean` (`ProperCone.hyperplane_separation_point` de Mathlib)

## Notes

- Le théorème de Bondareva-Shapley est clos dans les deux directions (`forward` + `backward`), **0 sorry**. La direction `←` extrayait une allocation du Cœur par un argument de Farkas / séparation d'hyperplan sur un cône ; cet argument, longtemps tagué **INTRACTABLE**, est désormais construit et prouvé dans `CooperativeGames/ConeKernel.lean` (cône augmenté `augCone`, lemme dual `augCone_dual_iff`, séparateur `separatingFunctional_none_neg`, décodage du témoin `exists_preimputation_strict_core`)
- Arc de preuve : PR #3933 (noyau ConeKernel, TUGame-free) → #3941 (pont `balancedUnit`) → #3945 (cœur du décodage) → #3951 (câblage du pipeline) → #3954 (sorry 1→0). `hb_witness` est désormais un `have` certifié (`Basic.lean:348`)
- Lié à `stable_marriage_lean/` (théorie des appariements comme jeu coopératif)

## Conclusion

Ce projet formalise la théorie des jeux coopératifs en Lean 4 — la **valeur de Shapley**
(close, 0 `sorry`) et le **Cœur** avec le **théorème de Bondareva-Shapley** (0 `sorry`,
prouvé dans les deux directions). Il compile avec `lake build CooperativeGames` sur
Mathlib4 (toolchain `v4.30.0-rc2`).

### Ce qui est prouvé

- **Unicité de la valeur de Shapley** (`Shapley.lean`, 0 `sorry`) : la valeur de Shapley
  est l'allocation *unique* satisfaisant efficacité, symétrie, joueur nul et additivité —
  la caractérisation axiomatique de Shapley (1953).
- **Cœur + théorème de Bondareva-Shapley** (`Basic.lean` + `ConeKernel.lean`) : jeu
  coopératif, fonction caractéristique, le Cœur et la condition de jeu équilibré (balanced),
  avec la direction `←` (balanced ⇒ Cœur non vide) **entièrement prouvée** par séparation de
  cône.

### Comment la direction backward a été prouvée

L'étape jadis taggée **INTRACTABLE** — extraire de la condition équilibrée une allocation
`x ∈ Core` avec `∑ xᵢ ≤ v(N)`, un argument de Farkas / séparation d'hyperplan sur un cône —
est désormais close. La machinerie vit dans `CooperativeGames/ConeKernel.lean` : le cône
augmenté `augCone` encode les violations de poids équilibrés, et
`ProperCone.hyperplane_separation_point` (Mathlib `Analysis.Convex.Cone.Dual`) fournit un
séparateur `f` ; les lemmes de dualité (`augCone_dual_iff`), de séparateur non-négatif
(`separatingFunctional_none_neg`) et de décodage du témoin (`exists_preimputation_strict_core`)
convertissent ce séparateur en une imputation du Cœur. `hb_witness` est désormais un `have`
certifié (`Basic.lean:348`). Arc : #3933 → #3941 → #3945 → #3951 → #3954 (sorry 1→0). Le
plan d'origine reste documenté dans
[`docs/BONDAREVA_FARKAS_PLAN.md`](docs/BONDAREVA_FARKAS_PLAN.md).

### Où aller ensuite

- **Théorie** : Bondareva (1963) / Shapley (1967), les caractérisations du Cœur ;
  Shapley (1953), *A Value for n-Person Games*.
- **Plan actif** : [`docs/BONDAREVA_FARKAS_PLAN.md`](docs/BONDAREVA_FARKAS_PLAN.md)
  et [`FORMAL_STATUS.md`](FORMAL_STATUS.md).
- **Lié** : [`stable_marriage_lean/`](../stable_marriage_lean/) (appariement Gale-Shapley)
  et [`social_choice_lean/`](../social_choice_lean/) (Arrow / Sen).
