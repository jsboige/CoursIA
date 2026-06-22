# Cooperative Games Lean

Formalisation en Lean 4 de la théorie des jeux coopératifs (valeur de Shapley, cœur).

## Statut

- **Toolchain** : v4.30.0-rc2
- **Compte de sorry** : 1 en production (`Basic.lean` L312, `bondareva_shapley_forward.hCore`, taggé `INTRACTABLE_UNTIL_BONDAREVA_HYPERPLANE_SEPARATION`)
- **Build** : `lake build CooperativeGames` — SUCCESS
- **Dépendances** : Mathlib4

## Modules

| Fichier | sorry | Description |
|---------|-------|-------------|
| `CooperativeGames/Shapley.lean` | 0 | Définition de la valeur de Shapley et théorème d'unicité |
| `CooperativeGames/Basic.lean` | 1 | Jeu coopératif / fonction caractéristique / Cœur / scaffolding Bondareva-Shapley |

## Résultats clés

- **Unicité de la valeur de Shapley** : prouvé que la valeur de Shapley est l'unique valeur satisfaisant les axiomes d'efficacité, symétrie, joueur nul et additivité (Shapley.lean, 0 sorry)
- **Définitions du Cœur** : jeu coopératif, fonction caractéristique, ensemble des joueurs, Cœur (Basic.lean)
- **Direction `←` de Bondareva-Shapley** (balanced ⇒ Cœur non vide) : tout le scaffolding est clos sauf la dernière étape d'extraction en L312

## Notes

- Le `sorry` isolé vit dans `bondareva_shapley_forward.hCore` (Basic.lean L312). La preuve ramène « P ⊆ {x : ∑ xᵢ ≥ v(N)} » à l'extraction d'une allocation avec égalité, ce qui requiert soit une séparation d'hyperplan de type Farkas, soit un argument constructif d'existence d'un minimum sur un compact convexe
- Mathlib4 ne dispose pas actuellement du lemme de séparation d'hyperplan requis ; taggé **INTRACTABLE** par le prouveur multi-agents en attendant que cette infrastructure arrive (cf [LEAN_INVENTORY.md](../LEAN_INVENTORY.md) table GO/NO-GO)
- Lié à `stable_marriage_lean/` (théorie des appariements comme jeu coopératif)

## Conclusion

Ce projet formalise la théorie des jeux coopératifs en Lean 4 — la **valeur de Shapley**
(close, 0 `sorry`) et le **Cœur** avec le **théorème de Bondareva-Shapley** (1 `sorry`,
WIP). Il compile avec `lake build CooperativeGames` sur Mathlib4 (toolchain
`v4.30.0-rc2`).

### Ce qui est prouvé

- **Unicité de la valeur de Shapley** (`Shapley.lean`, 0 `sorry`) : la valeur de Shapley
  est l'allocation *unique* satisfaisant efficacité, symétrie, joueur nul et additivité —
  la caractérisation axiomatique de Shapley (1953).
- **Cœur + scaffolding Bondareva-Shapley** (`Basic.lean`) : jeu coopératif, fonction
  caractéristique, le Cœur et la condition de jeu équilibré (balanced), avec la direction
  `←` (balanced ⇒ Cœur non vide) ramenée à une seule étape d'extraction.

### Pourquoi le sorry isolé reste

L'unique `sorry` (`Basic.lean:312`, `hb_witness`) est le **noyau LP-dual** de la
direction backward de Bondareva-Shapley : extraire de la condition équilibrée une
allocation `x ∈ Core` avec `∑ xᵢ ≤ v(N)`. C'est un argument de Farkas / séparation
d'hyperplan sur un cône. Il est **WIP, pas abandonné** — un plan actif
([`docs/BONDAREVA_FARKAS_PLAN.md`](docs/BONDAREVA_FARKAS_PLAN.md)) valide
l'infrastructure (`ProperCone.hyperplane_separation_point` via un encodage
`(Option N) → ℝ`) et isole la traduction restante (~150-180 lignes ; l'étape
`StrongDual → balanced weights` est le point crucial). `FORMAL_STATUS.md` l'enregistre
comme WIP_HARD.

### Où aller ensuite

- **Théorie** : Bondareva (1963) / Shapley (1967), les caractérisations du Cœur ;
  Shapley (1953), *A Value for n-Person Games*.
- **Plan actif** : [`docs/BONDAREVA_FARKAS_PLAN.md`](docs/BONDAREVA_FARKAS_PLAN.md)
  et [`FORMAL_STATUS.md`](FORMAL_STATUS.md).
- **Lié** : [`stable_marriage_lean/`](../stable_marriage_lean/) (appariement Gale-Shapley)
  et [`social_choice_lean/`](../social_choice_lean/) (Arrow / Sen).
