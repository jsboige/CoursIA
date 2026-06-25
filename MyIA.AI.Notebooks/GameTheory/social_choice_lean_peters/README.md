# Choix Social Lean (référence Peters)

Projet de référence important [`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean)
comme dépendance Lake. Visite guidée (« curated tour ») des résultats formalisés
de Peters.

## Statut

- **Toolchain** : `leanprover/lean4:v4.27.0-rc1` (pinnée sur la version de Peters)
- **Compte de sorry** : 0 sorry en production
- **Build** : `lake build` — SUCCESS
- **Dépendances** : Mathlib4, `DominikPeters/SocialChoiceLean`

## Modules

| Fichier | sorry | Description |
|---------|-------|-------------|
| `PetersTour.lean` | 0 | Visite guidée des résultats formalisés de Peters |

## Résultats clés

Importe et illustre la bibliothèque de Peters, notamment :

- **Gibbard-Satterthwaite** : la résistance à la manipulation (« strategy-proofness ») implique la dictature (≥ 3 candidats)
- **Duggan-Schwartz** : extension multi-vainqueurs avec résistance à la manipulation optimiste/pessimiste
- **4 impossibilités de Condorcet** : Participation, Renforcement, Résistance à la manipulation, Anonymat+Neutralité+Resoluteness
- **15+ règles de vote** avec vérification d'axiomes : Split Cycle, Schulze, Copeland, Black, IRV, Borda, etc.

## Relation avec `social_choice_lean`

Complémentaire, sans doublon. `social_choice_lean` utilise un `PrefOrder` personnalisé (nos preuves) ; ce projet utilise le `LinearOrder` de Peters (référence externe). Cadres différents, preuves différentes.

## Notes

- Backend Lake pour un notebook compagnon de tour (prévu, pas encore créé)
- Le dépôt de Peters est pinné au commit `d679d950` pour la reproductibilité
- Peters utilise `LinearOrder` (strict, Mathlib) ; nous utilisons `PrefOrder` (réflexif, total, transitif)

## Conclusion

Ce projet est une **visite de référence** de
[`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean),
importée comme dépendance Lake (pinnée au commit `d679d950`, toolchain
`v4.27.0-rc1`) et exhibée via des `#check` dans `PetersTour.lean` — **0 `sorry`**,
`lake build` SUCCESS. Ce n'est **pas** une formalisation originale : il présente
les résultats de Peters, l'implémentation de référence actuelle de la théorie du
choix social en Lean 4.

### Ce que la visite couvre

- **Gibbard-Satterthwaite** — la résistance à la manipulation implique la
  dictature (≥ 3 candidats) ;
- **Duggan-Schwartz** — extension multi-vainqueurs avec résistance à la
  manipulation optimiste/pessimiste ;
- **4 impossibilités de Condorcet** — Participation, Renforcement, Résistance à
  la manipulation, Anonymat+Neutralité+Resoluteness ;
- **15+ règles de vote** avec vérification d'axiomes (Split Cycle, Schulze,
  Copeland, Black, IRV, Borda, …).

### Complémentaire, pas doublon

Ce projet et [`social_choice_lean/`](../social_choice_lean/) couvrent la même
théorie au travers de **cadres différents** : Peters utilise le `LinearOrder`
strict de Mathlib, tandis que `social_choice_lean/` utilise le `PrefOrder`
réflexif-total-transitif (plus proche de la tradition d'économie du bien-être).
Lire les deux montre comment le choix du cadre modèle les définitions et les
preuves.

### Où aller ensuite

- **Notebook compagnon** : prévu (pas encore créé) — un tour pédagogique des résultats
  de Peters, auquel ce projet servirait de backend.
- **Amont** : [`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean) (MIT).
- **Nos preuves** : [`social_choice_lean/`](../social_choice_lean/) — Arrow / Sen /
  électeur médian dans le cadre `PrefOrder`.
