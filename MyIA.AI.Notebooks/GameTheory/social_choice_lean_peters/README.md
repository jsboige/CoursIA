# Choix Social Lean (référence Peters)

Projet de référence important [`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean)
comme dépendance Lake. Visite guidée (« curated tour ») des résultats formalisés
de Peters.

## Statut

> **État mesuré au 2026-09-26 — la cible de toolchain du parc est passée à `v4.33.0` (EPIC #14773)
> et ce lake ne peut pas suivre. Il est désormais une *exception documentée* du parc, et non plus
> un lake « convergé ».**

- **Toolchain** : `leanprover/lean4:v4.32.1` — pin effectif du `lean-toolchain`, mais **en retard sur
  la cible du parc** (`v4.33.0`). L'écart est mesuré, sa cause est amont, et il est documenté ci-dessous.
- **Compte de sorry** : 0 sorry en production
- **Build** : `lake build` — SUCCESS à `v4.32.1` (le pin effectif)
- **Dépendances** : Mathlib4 (`520045ab14e2`), `DominikPeters/SocialChoiceLean` (`94a4c650b6a3`) — revs effectives du `lake-manifest.json`

### Pourquoi ce lake reste à `v4.32.1` (mesuré, 2026-09-26)

La migration vers `v4.33.0` a été **tentée et instrumentée** : `lean-toolchain` basculé, les huit
dépendances transitives explicitées (bloc `require … from git … @ <rev>` aux révisions du parc, pour
que nos revs l'emportent sur celles charriées par le manifest de `SocialChoiceLean`), `lake update`,
`lake exe cache get`, puis `lake build`. Le contournement de version a **fonctionné** — les erreurs
ont quitté `Batteries.Tactic.Alias`, `Qq.Typ` et `ProofWidgets.Component.MakeEditLink` — et ont
révélé une incompatibilité **réelle, dans les sources amont** :

```
error: SocialChoice/Margin.lean:277:10: Tactic `rfl` failed
error: SocialChoice/Margin.lean:281:10: Type mismatch
error: SocialChoice/Margin.lean:313:10: Tactic `rfl` failed
error: SocialChoice/Margin.lean:317:10: Type mismatch
error: SocialChoice/Margin.lean:756:8:  Tactic `rfl` failed
error: SocialChoice/Margin.lean:759:8:  Tactic `rfl` failed
error: SocialChoice/Impossibilities/GibbardSatterthwaite/InductionStepCase2.lean:1286:2: unsolved goals
error: SocialChoice/Impossibilities/GibbardSatterthwaite/InductionStepCase2.lean:1288:2: unsolved goals
```

La classe d'erreur est unique et cohérente : les buts résiduels opposent la somme indexée
`V ⊕ Unit` au type nu `V` — par exemple
`⊢ Sum.inr w ∈ {v | a < b} ↔ w ∈ {v | a < b}` — soit un changement de la normalisation de `filter`
sur les sommes dans Mathlib 4.33. La compilation atteint `[3029/3044]` avant d'échouer.

**Ces fichiers ne sont pas les nôtres.** Ce sont ceux du paquet externe
[`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean), épinglé à
`94a4c650b6a3` (dernier commit amont du 2026-07-21, « Clean up Lean 4.32 warnings » ; branches
disponibles `master`, `duggan-schwartz`, `claude/formalize-duggan-schwartz-AyuSa` — aucune ne porte
de portage 4.33). On **ne patche pas** du code *vendored* : le verdict est **bloqué en amont**, et il
est rapporté comme tel sur l'EPIC #14773 plutôt que contourné ici.

**Conséquence** : le `v4.32.1` de ce lake est une **exception assumée** jusqu'à ce que l'amont
publie un état compatible 4.33. Ce n'est pas un défaut de ce dépôt, et ce n'est pas réparable ici.

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
- Le dépôt de Peters est référencé au commit `94a4c650b6a3ef14df801a613c3b46169dbd754d` (rev du `lake-manifest.json`) pour la reproductibilité
- Peters utilise `LinearOrder` (strict, Mathlib) ; nous utilisons `PrefOrder` (réflexif, total, transitif)

## Statut EPIC #4365 (anti-proliferation GT 6→2)

Ce lake est **explicitement hors du périmètre d'absorption** dans
[`game_theory_lean/`](../game_theory_lean/) au titre de l'EPIC #4365 Phase 4
(regrouper les lakes cohesifs post-convergence). L'historique du statut :

1. **Verrouillage amont (`INTRINSIC`, levé depuis)** : au moment de la
   décision (c.576, 2026-07-17), le dépôt externe
   [`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean)
   était pinné à `355075e3` sur la famille `v4.27.0-rc1`, et son port vers la
   cible post-#4364 n'était pas sous notre contrôle — verdict `INTRINSIC` au
   sens de [`sota-not-workaround.md`](../../../.claude/rules/sota-not-workaround.md).
   **Ce verrou a été levé par l'amont lui-même** : depuis le 2026-08-21
   (#12134, commit `d8ec0b08ba`), le pin effectif est Peters `94a4c650` /
   Mathlib `520045ab` sur `lean-toolchain` `v4.32.1` — la famille du reste
   du parc. La convergence #4364 s'applique désormais ici aussi ; peters
   n'est plus résidu v4.27.
   *(Addendum 2026-09-26 : cette phrase était vraie le 2026-08-21, quand la
   cible du parc était `v4.32.1`. Depuis que la cible est passée à `v4.33.0`
   (EPIC #14773), elle ne l'est plus — voir le bloc « Pourquoi ce lake reste à
   `v4.32.1` » au §Statut. L'historique est conservé ci-dessus tel qu'il a été
   écrit.)*

2. **Cadre sémantique distinct (toujours actif)** : ce lake expose un
   `LinearOrder` strict (Mathlib) qui **n'est pas** compatible avec l'API
   `PrefOrder` réflexif-total-transitive utilisée par
   `game_theory_lean/SocialChoice/`. Une fusion forcerait soit (a) un
   double-port linéaire/préf-ordre, soit (b) une ré-écriture des preuves de
   Peters. **C'est le motif d'autonomie qui demeure** après la convergence de
   toolchain : ce lake est un *port externe* (les preuves sont celles de
   Peters) quand `game_theory_lean/` porte nos preuves.

**Conséquence** : `social_choice_lean_peters/` reste un **lake autonome
auto-suffisant** avec son propre `lake build`, son propre `lean-toolchain`
`v4.32.1` (**exception documentée**, cf. bloc « Pourquoi ce lake reste à
`v4.32.1` » au §Statut), et son propre CI. L'autonomie n'est plus motivée par un
verrou de version — elle est motivée par la nature du projet : une visite de
référence d'une bibliothèque externe, dans son propre cadre sémantique.

Statut vérifié firsthand (2026-08-26) : `lake-manifest.json` Peters rev
`94a4c650b6a3ef14df801a613c3b46169dbd754d`, Mathlib rev
`520045ab14e26149ee970e2e617ca04b09bde5d6`, `lean-toolchain` = `v4.32.1`,
`PetersTour.lean` + `PetersTour_en.lean` (i18n #4980), 0 sorry — **le statu
quo est intentionnel et documenté**, pas un oubli.

Voir aussi : [`#4365`](https://github.com/jsboige/CoursIA/issues/4365) (cible
de regroupement GT 6→2), [`#4364`](https://github.com/jsboige/CoursIA/issues/4364)
(convergence Mathlib — `COMPLETED 2026-07-03`), [`#4362`](https://github.com/jsboige/CoursIA/issues/4362)
(EPIC parent « Lean — harmoniser Mathlib, regrouper les lakes »).

## Conclusion

Ce projet est une **visite de référence** de
[`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean),
importée comme dépendance Lake (pinnée au commit `94a4c650b6a3ef14df801a613c3b46169dbd754d`, toolchain
`v4.32.1`) et exhibée via des `#check` dans `PetersTour.lean` — **0 `sorry`**,
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
