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
- Le dépôt de Peters est pinné au commit `355075e3e35f940a2ade0cbfb5be27b4a53c6776` pour la reproductibilité
- Peters utilise `LinearOrder` (strict, Mathlib) ; nous utilisons `PrefOrder` (réflexif, total, transitif)

## Statut EPIC #4365 (anti-proliferation GT 6→2)

Ce lake est **explicitement hors du périmètre d'absorption** dans
[`game_theory_lean/`](../game_theory_lean/) au titre de l'EPIC #4365 Phase 4
(regrouper les lakes cohesifs post-convergence), pour deux raisons cumulatives :

1. **Verrouillage amont (`INTRINSIC`)** : ce lake **importe** le dépôt
   [`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean)
   pinné au commit `355075e3e35f940a2ade0cbfb5be27b4a53c6776` (rev effectif
   dans `lake-manifest.json`), qui dépend d'un Mathlib de la famille
   `v4.27.0-rc1`. Le port de cet amont vers `v4.31.0-rc1` (cible post-#4364)
   n'est **pas** sous notre contrôle — c'est un projet externe (MIT, Dominik
   Peters) et le port est potentiellement lourd (4 révisions d'écart, multiples
   ruptures d'API). **Verdict `INTRINSIC`** au sens de
   [`sota-not-workaround.md`](../../../.claude/rules/sota-not-workaround.md)
   : pas de chemin SOTA réel pour absorber sans casser la dépendance.

2. **Cadre sémantique distinct** : ce lake expose un `LinearOrder` strict
   (Mathlib) qui **n'est pas** compatible avec l'API `PrefOrder` réflexif-total-
   transitive utilisée par `game_theory_lean/SocialChoice/`. Une fusion forcerait
   soit (a) un double-port linéaire/préf-ordre, soit (b) une ré-écriture des
   preuves de Peters — au-delà du budget « PR atomique R3 ».

**Conséquence** : `social_choice_lean_peters/` reste un **lake autonome
auto-suffisant** avec son propre `lake build`, son propre `lean-toolchain`
`v4.27.0-rc1`, et son propre CI. La convergence #4364 Phase 3 (10 lakes rc2
bumps vers `d568c8c0` / `v4.31.0-rc1`, complétée 2026-07-03 par un autre
worker) **ne s'applique pas** ici — peters est le seul résidu v4.27 du parc.

Statut vérifié firsthand (c.576, 2026-07-17) : `lake-manifest.json`
pinné sur le commit Peters `355075e3e35f940a2ade0cbfb5be27b4a53c6776` (rev),
Mathlib rev `8cb9319191fd34b6f23d7ffea58a4f8fb674cefd`, `lean-toolchain` =
`v4.27.0-rc1`, `PetersTour.lean` 234 lignes, 0 sorry (grep vérifié),
build SUCCESS — **le statu quo est intentionnel et documenté**, pas un
oubli.

Voir aussi : [`#4365`](https://github.com/jsboige/CoursIA/issues/4365) (cible
de regroupement GT 6→2), [`#4364`](https://github.com/jsboige/CoursIA/issues/4364)
(convergence Mathlib — `COMPLETED 2026-07-03`), [`#4362`](https://github.com/jsboige/CoursIA/issues/4362)
(EPIC parent « Lean — harmoniser Mathlib, regrouper les lakes »).

## Conclusion

Ce projet est une **visite de référence** de
[`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean),
importée comme dépendance Lake (pinnée au commit `355075e3e35f940a2ade0cbfb5be27b4a53c6776`, toolchain
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
