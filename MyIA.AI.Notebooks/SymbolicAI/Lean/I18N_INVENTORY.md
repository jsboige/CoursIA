# Inventaire i18n des projets Lean 4 — couverture FR/EN

Inventaire transverse de la **couverture i18n** (FR canonique + EN sibling) des
fichiers `.lean` de nos lakes, à la date **2026-07-15**, dernier recompte firsthand
**2026-08-28** (§ refresh ↻08-28 ci-dessous). Source de vérité :
conventions ratifiées par ai-01 (2026-07-04, issue
[#4980](https://github.com/jsboige/CoursIA/issues/4980) comment-4881909354).

## Contexte et convention

La convention i18n Lean retenue (cf. PR #6048 `RepeatedGames` c.356) impose, pour
chaque fichier `Foo.lean` :

- `Foo.lean` : **FR canonique** (namespace par défaut du module)
- `Foo_en.lean` : **EN sibling** (namespace `…_en`, **non-docstring content
  byte-identical** au FR)
- **Drift-CI détectable** : le contenu non-docstring des deux siblings doit rester
  byte-identique. Une PR qui modifie uniquement le FR (ou uniquement l'EN) sans
  mettre à jour l'autre → CHANGES_REQUESTED (cf. `lean-merge-discipline §1`).
- **Hors scope** (cf. `readme-french-first.md`) : libs vendored (`.lake/packages/**`),
  lakes externes (`_peters`, etc.), forks untracked.

Issue parente : [#4980](https://github.com/jsboige/CoursIA/issues/4980) (open,
tranche 1/3 = cet inventaire). Tranches suivantes : (2) proposition de convention
détaillée par type de lake, (3) PR pilote sur un lake cible.

---

## Résumé par lake (scope inventaire historique)

| Lake | FR canonique | EN sibling | Couverture fichiers | Statut |
|------|-------------:|-----------:|--------------------:|--------|
| `learning_theory_lean` | 18 | 18 | 18/18 = **100 %** | EXCELLENT ↻07-17 |
| `game_theory_lean` | 28 | 21 | 21/28 = **75 %** | EXCELLENT (multi-lib ; a absorbé RepeatedGames #6146 + CooperativeGames + SocialChoice ; les 7 sans sibling = 3 agrégateurs racine type-D + `_SmokeTest` harness + `Swaps`×2 et `SocialChoice/AMD` substantiels) ↻08-28 |
| `sudoku_lean` | 4 | 4 | 4/4 = **100 %** | EXCELLENT ↻07-17 |
| `minimax_lean` | 4 | 4 | 4/4 = **100 %** | EXCELLENT ↻07-17 |
| `knot_lean` | 7 | 7 | 7/7 = **100 %** | EXCELLENT (⬆ 0→6 : po-2025 #6429/#6440 livrés — bilinguisation complète) ↻07-17 |
| `sensitivity_lean` | 5 | 5 | 5/5 = **100 %** | EXCELLENT ↻07-17 |
| `conway_lean` | 39 | 32 | 32/39 = **82 %** | EXCELLENT (**tous les modules pédagogiques + satellites couverts** — 32/32 paires OK au checker ; les 7 sans sibling sont la machinerie prover EN-first recherche : `HashlifeCorrectness.lean` 7434-L, `Foundation.lean`, `Walls`×4, `JumpCapture.lean`) ↻08-28 |
| `calibration_lean` | 4 | 4 | 4/4 = **100 %** | EXCELLENT ↻07-17 |
| `grothendieck_lean` | 60 | 59 | 59/60 = **98 %** | EXCELLENT (les 9 type-B EN-canon → FR-flip signalés le 15/07 sont **livrés** ; seul le root agrégateur `Grothendieck.lean` type-D reste sans sibling — modules 59/59 = 100 %) ↻08-28 |
| `conway_cgt_lean` | 1 | 1 | 1/1 hors lakefile = **100 %** | **FAIT** (⬆ 0→1 : `CGTTour_en.lean` livré — l'ancien « pilote #1 » est clos) ↻08-28 |
| `finiteness_lean` | 2 | 1 | 1/2 = **50 %** | BON (1 utilitaire interne non traduit) ↻07-17 |
| `mathlib_examples` | 2 | 1 | 1/2 = **50 %** | BON (`Basic_en.lean` livré #6664 ; seul le root umbrella `MathLibExamples.lean` reste sans sibling) ↻07-17 |
| `repeated_games_lean` | 1 | 1 | — | **ABSORBÉ** dans `game_theory_lean` (#6146, cf. #4365) — legacy quasi-vide |
| `social_choice_lean` | — | — | — | **ABSORBÉ / supprimé du scan** (0 fichier restant, #6040, cf. #4365) ↻08-28 |
| `cooperative_games_lean` | — | — | — | **ABSORBÉ / lake supprimé** — plus de `lakefile.lean` standalone ; contenu migré dans `game_theory_lean/CooperativeGames/` (cf. `code-style.md` §Lean) |
| `social_choice_lean_peters` | 1 | 1 | 1/1 = **100 %** | **HORS SCOPE** (vendored, `_peters`) — un sibling EN existe désormais ↻08-28 |
| `galois_lean` | 2 | 0 | 0/2 | **À FAIRE (léger)** ↻08-28 (nouveau lake suivi) — vendored `M23Lean4Web.lean` EN-first (Apache-2.0, hors scope traduction) + root agrégateur `Galois.lean` type-D ; « siblings `_en` à venir » cf README du lake |
| `mimo_lean` | 6 | 6 | 6/6 = **100 %** | EXCELLENT ↻08-28 (nouveau lake suivi) |
| `assignment_lean` | 5 | 5 | 5/5 = **100 %** | EXCELLENT ↻08-28 (nouveau lake suivi, `GameTheory/`) |
| `asymmetric_information_lean` | 6 | 6 | 6/6 = **100 %** | EXCELLENT ↻08-28 (nouveau lake suivi, `GameTheory/`) |

> **Refresh 2026-07-15 (ai-01, See #4980)** : recompte firsthand sur `origin/main`
> @ `77294f5941`. Changements majeurs vs epoch 2026-07-14 (`455492afa`) : (a)
> **`knot_lean` 0→6** et **`conway_cgt_lean` 0→1** — les deux anciens « candidats
> pilote À FAIRE » sont désormais **bilingualisés** (po-2025 #6429/#6440 + CGTTour_en
> livrés), donc les recommandations pilote de la version 14/07 sont **caduques** ;
> (b) `conway_lean` 11→18 (+7), `grothendieck_lean` 12→15 (+3), `game_theory_lean`
> 19→21 (+2) — bilinguisation incrémentale en cours sur les 3 gros lakes ; (c)
> `cooperative_games_lean` n'a **plus de `lakefile.lean` standalone** (absorption
> complète #6274, disparu du scan) — retiré de « BON », reclassé ABSORBÉ. Les comptes
> `fr_files` incluent `lakefile.lean` (aglistique) — un `fr=en=1` sur un legacy
> signifie « dir quasi-vide post-absorption », pas « lake actif sans i18n ».

> **Refresh 2026-07-17 (po-2024, See #4980)** : recompte firsthand sur `origin/main`
> @ `aede9bfc7` (scan `find … *.lean` hors `.lake`, FR = hors `*_en.lean` et hors
> `lakefile`, EN = `*_en.lean`, couverture = FR ayant un sibling `${base}_en.lean`).
> La table ci-dessus est **corrigée** — l'inventaire 2026-07-15 sous-estimait
> massivement la couverture réelle. Principaux écarts : (a) **`conway_lean` 64 %→96 %**
> — les 5 grains type-C propres identifiés le 15/07 (`Doomsday`, `Fractran`,
> `FreeWillTheorem`, `LookAndSay`, `Nim`) sont **désormais livrés** ; seul
> `Conway/Life/HashlifeCorrectness.lean` (3790 lignes, preuve recherche EPIC #6724
> GOL-S4) reste sans sibling — cible prover, pas un grain i18n. (b) **`grothendieck_lean` 58 %→92 %**
> (+8 siblings livrés). (c) **`knot_lean` 75 %→100 %**, **`decision_theory_lean` 92 %→100 %**
> (Coherence/Gittins/Utility complets via #6154/#6138). (d) **`mathlib_examples` 0 %→50 %**
> (`Basic_en.lean` livré #6664 — n'est plus « À FAIRE 0 % »). **Bilan** : le rollout
> i18n pédagogique (#4980) est **quasi-complet** ; il ne reste **aucun grain type-A
> clean** sur les lakes suivis sauf `lean_game_defs_ext` (voir table hors scope
> ci-après) et les type-B FR-flips recherche (grothendieck, basse priorité).
>
> ⚠ **Nouveau grain découvert — `lean_game_defs_ext` (GameTheory/), 0/13 = 0 %** :
> lake bayésien FR-canon (docstrings FR, type-A léger), **absent de l'inventaire
> 2026-07-15**. Le root `Bayesian.lean` est **bilingue inline (Option B)** — un
> grain clean = split en sibling pair FR-seul + `Bayesian_en.lean` (le bloc EN
> migre, pas de régression). **Caveat build** : `lakefile.toml` n'a pas de `globs`
> → le sibling root `_en` ne serait PAS type-checké par la CI sans ajouter
> `globs = ["Bayesian.*", "Bayesian_en"]` (pattern #6585, cf `decision_theory_lean`).
> Syntaxe TOML globs **non encore éprouvée dans le repo** (aucun lakefile.toml
> n'utilise globs) → router vers une lane Lean-build-capable (po-2023/po-2026) pour
> livrer le grain + vérifier le build.

> **Refresh 2026-08-28 (po-2024, See #13211)** : recompte firsthand sur `origin/main`
> @ `c9811ce1ff` (même script de reproduction, § « Inventaire brut » — sortie
> complète 08-28 en fin de fichier). La table ci-dessus est **corrigée**. Principaux
> changements vs 07-17 : (a) **`lean_game_defs_ext` 0/13 → 13/13** — le grain
> type-C « À FAIRE » (split `Bayesian.lean` bilingue-inline) est **livré**, la cible
> pilote de la version 17/07 est **caduque** ; (b) **`grothendieck_lean` 92 % → 98 %**
> (59/60) — les 9 modules type-B EN-canon déclassés « basse priorité » le 15/07 ont
> été **flippés et livrés** ; seul le root agrégateur type-D reste sans sibling ;
> (c) **`conway_lean` 26/27 → 32/39** — l'expansion prover b3'/c.95/c.1035 a ajouté
> 7 fichiers machinerie EN-first sans sibling (`Foundation`, `Walls`×4,
> `JumpCapture`, `HashlifeCorrectness` 7434 L) ; **tous les modules pédagogiques
> restent couverts** (32/32 paires OK au checker `check_i18n_siblings.py`) ;
> (d) **4 nouveaux lakes suivis** : `assignment_lean` (5/5), `asymmetric_information_lean`
> (6/6), `mimo_lean` (6/6), `galois_lean` (2/0 — vendored `M23Lean4Web` EN-first +
> root agrégateur, « siblings `_en` à venir » cf son README) ; (e) complétions de
> queue : `decision_theory` 92→100 %, `search` 83→100 %, `planning` 75→100 %,
> `kelly` 75→100 %, `erc20` 60→100 %, `argumentation` 71→83 % (5/6) ;
> (f) `social_choice_lean` a **disparu du scan** (absorption complète, 0 fichier) ;
> `social_choice_lean_peters` (vendored, hors scope) porte désormais un sibling
> `PetersTour_en.lean`.

---

## Nature des gaps restants — FR-flip vs EN-sibling (2026-07-15, ai-01 firsthand)

**Le compte « N siblings restants » de la table Résumé conflate quatre types de gap
très différents.** Un audit firsthand (`git ls-files` + lecture des headers de
docstring, pas un grep buggé) le 2026-07-15 montre que le « reste à faire » nominal
sur les deux gros lakes n'est PAS un chantier de traduction FR→EN propre. Distinguer :

| Type de gap | Définition | Effort | Priorité |
|-------------|-----------|--------|----------|
| **(A) FR-canon → EN-sibling** | `Foo.lean` a des docstrings **FR canoniques**, pas de `Foo_en.lean` | Léger (traduire FR→EN, tactiques byte-identical) | **Grain clean 1-PR** |
| **(B) EN-canon → FR-flip** | `Foo.lean` a des docstrings **anglaises** (fichier authored EN-first) | Lourd (flip FR canonique + EN sibling) | **Basse** (surtout lake recherche) |
| **(C) bilingue inline** | `Foo.lean` contient EN **et** FR dans le même fichier (état Option B hybride) | Léger-moyen : split → base FR-seule + `Foo_en.lean` EN-seul | **Grain clean** sur lake PEDA sous greenlight #4980 (Option B **rejetée** → à convertir) ; **cosmétique** seulement sur lake REF/harness sans greenlight |
| **(D) aglistique** | `lakefile.lean`, umbrella `Foo.lean` sans docstring utilisateur | N/A (pas de sibling par convention) | Hors compte |

**Conséquence sur les deux gros lakes :**

- **`grothendieck_lean` (10 nominal)** : les **9 modules substantiels NO-EN sont TOUS
  de type (B) EN-canoniques** (headers `« Grothendieck tribute — Part N: … »`,
  docstrings anglaises — vérifié firsthand sur `CanonicalProps`, `MathlibMap`,
  `SheafBasics`, `SheafCohomology/MayerVietoris`, `Sheafification`, `SieveGenerate`,
  `SieveLattice`, `SieveOps`, `YonedaLemma`). Ce n'est **pas** un gap EN-sibling
  propre : c'est un FR-flip lourd sur un lake **recherche** (EPIC #2159) → priorité
  **basse** (cf `readme-french-first.md` : la francisation vise en priorité la prose
  pédagogique, pas le retro-flip de fichiers Lean recherche EN-first). Le reste (umbrella
  + lakefile) = type (D).
- **`conway_lean`** : audit firsthand **exhaustif** 2026-07-15 (lecture complète des
  docstrings, pas un peek de header) — les **6 fichiers non-Life sont TOUS de type (C)
  bilingue inline** (bloc EN en tête + bloc FR substantiel) : `CollatzLike`, `Doomsday`,
  `Fractran`, `FreeWillTheorem`, `LookAndSay`, `Nim`. Sous le greenlight option-c #4980
  (Option B **rejetée**), ce sont **des grains sibling-extraction CLEAN**, PAS « déjà
  couverts ». `CollatzLike_en` est livré (#6663) mais **extract-only** (le bloc EN
  subsiste dans la base `CollatzLike.lean`, marqueur « This module formalizes the »
  présent) → il reste **5 grains** : `Doomsday`, `Fractran`, `FreeWillTheorem`,
  `LookAndSay`, `Nim`. Cible convention-pure = `Angel.lean` (**FR-seul**, vérifié
  firsthand) + `Angel_en.lean` : pour chaque fichier, créer `Foo_en.lean` EN-seul **et
  retirer le bloc EN de la base** (le bloc EN migre dans le sibling → aucune perte de
  contenu, ce n'est pas une régression). Lake **PEDA** haute valeur, **lane active
  po-2026** → `[CLAIMED]` **par fichier** obligatoire (anti-double-claim R3).
- **Queues « near-done » (priorité 3, « 1-2 restants »)** : les résidus scannés sont
  en fait des **umbrellas/lakefiles type (D)** (ex. `argumentation_lean/Argumentation.lean`
  = umbrella `/-! … -/`), pas des gaps substantiels. Ces lakes sont **effectivement
  complets** côté modules.

**Bilan honnête** : le rollout i18n **pédagogique** (#4980) avance mais n'est **pas
épuisé**. Le « reste » substantiel réel = (a) `conway_lean` = **5 grains type-C clean**
(bilingue-inline → sibling, sous greenlight, lane po-2026) ; (b) `grothendieck_lean`
type-B FR-flips, recherche, basse priorité. Un worker sur la lane conway a **du grain
clean** : il **continue conway** (`[CLAIMED]` par fichier), il ne pivote PAS cross-lane
en invoquant une « saturation » que cet audit réfute. Le pivot cross-lane (pool global)
ne s'active **qu'après** livraison des 5 grains conway ET déclassement grothendieck.
Voir la révision de la table _Cibles PR pilote_.

---

## Lakes Lean hors scope inventaire historique (à intégrer — See #4980)

L'inventaire d'origine ne scannait que `SymbolicAI/Lean/`, `GameTheory/`, `ML/`,
`Sudoku/`. Le recompte 2026-07-15 révèle **6 lakes Lean supplémentaires** répartis
dans d'autres familles, tous déjà largement bilingualisés (la convention `_en`
sibling s'est propagée au-delà du périmètre initial). Ils sont désormais suivis ici.

| Lake | Famille | FR | EN | Couverture | Statut |
|------|---------|---:|---:|-----------:|--------|
| `decision_theory_lean` | `Probas/` | 13 | 13 | 13/13 = **100 %** | EXCELLENT ↻08-28 |
| `search_lean` | `Search/` | 5 | 5 | 5/5 = **100 %** | EXCELLENT ↻08-28 |
| `planning_lean` | `SymbolicAI/Planners/` | 3 | 3 | 3/3 = **100 %** | EXCELLENT ↻08-28 |
| `kelly_lean` | `QuantConnect/` | 3 | 3 | 3/3 = **100 %** | EXCELLENT ↻08-28 |
| `argumentation_lean` | `SymbolicAI/Tweety/` | 6 | 5 | 5/6 = **83 %** | BON ↻08-28 |
| `erc20_lean` | `SymbolicAI/SmartContracts/` | 4 | 4 | 4/4 = **100 %** | EXCELLENT ↻08-28 |
| `lean_game_defs` | `GameTheory/` | 6 | 6 | 6/6 = **100 %** | EXCELLENT ↻07-17 |
| `lean_game_defs_ext` | `GameTheory/` | 13 | 13 | 13/13 = **100 %** | EXCELLENT ↻08-28 — le grain type-C « À FAIRE » du refresh 07-17 (split `Bayesian.lean` bilingue-inline) est **livré**. |

> Aucun de ces lakes n'était « à 0 % » : la couverture i18n du repo est **plus
> avancée** que ne le laissait croire le périmètre de scan initial. Le reste à faire
> sur cette tranche = quelques siblings de queue (1-2 par lake), pas un chantier.

---

## Détail par lake

### 1. `learning_theory_lean` — EXCELLENT (100 %) ↻08-28

**Chemin** : `MyIA.AI.Notebooks/ML/learning_theory_lean/`

**18 fichiers FR canoniques** (hors lakefile), **18 fichiers EN siblings** (`*_en.lean`) = 18/18. Seul le
`lakefile.lean` n'a pas de sibling (les lakefiles sont par convention
aglistiques — pas de docstrings utilisateur).

**Mantra** : "learning_theory_lean = Perceptron (Novikoff) + PacLearning
(Valiant), 0 sorry, canon i18n à 95 %". Le module qui sert de **référentiel de
convention** (option A = fichiers siblings) — c'est ici que la convention FR+EN
siblings a été validée en premier.

**Suivi** : aucun ajout nécessaire ; surveiller la dérive (Drift-CI byte-identity).

### 2. `game_theory_lean` — EXCELLENT (75 %) ↻08-28

**Chemin** : `MyIA.AI.Notebooks/GameTheory/game_theory_lean/`

**Multi-lib lean** (cf. c.299 StableMarriage + c.306 CooperativeGames +
c.357 SocialChoice regroupement) : **28 fichiers FR canoniques**, **21 fichiers EN
siblings** (75 %) — les 7 sans sibling (↻08-28) = 3 agrégateurs racine type-D
(`GameTheory.lean`, `CooperativeGames.lean`, `SocialChoice.lean`), 1 harness
(`SocialChoice/_SmokeTest.lean`) et 3 substantiels (`Swaps.lean` + `Swaps/Basic.lean`
+ `SocialChoice/AMD.lean`). La convention `_en` namespace est appliquée par lean_lib
(`StableMarriage`, `CooperativeGames`, `SocialChoice` — chacun avec ses siblings
`_en`). Lake = pivot central du EPIC #4365 regroupement (a absorbé
`repeated_games_lean` #6146, `cooperative_games_lean` #6274, `social_choice_lean`
#6040).

**Mantra** : "game_theory_lean = cohorte multi-lib (StableMarriage +
CooperativeGames + SocialChoice), 0 sorry sur le théorème-phare, bilingue sur
21/26 modules". Les siblings restants sont listés ci-dessus (3 substantiels ↻08-28).

### 3. `sudoku_lean` — EXCELLENT (100 %) ↻08-28

**Chemin** : `MyIA.AI.Notebooks/Sudoku/sudoku_lean/`

**4 fichiers FR canoniques** (hors lakefile), **4 fichiers EN siblings** (`Sudoku.lean`,
`Basic.lean`, `Propagation.lean`, `ExactCover.lean`) = 4/4. Le `lakefile.lean` est
aglistique.

**Mantra** : "sudoku_lean = soundness propagation + exact-cover, 0 sorry, lake
pédagogique bilingue canon". Delta résiduel cosmétique seulement.

### 4. `minimax_lean` — EXCELLENT (100 %) ↻08-28

**4 fichiers FR canoniques** (hors lakefile), **4 fichiers EN siblings**. Coverage complète.

### 5. `knot_lean` — EXCELLENT (100 %) — bilinguisation livrée ↻08-28

**Chemin** : `MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/`

**7 fichiers FR canoniques** (hors lakefile), **7 fichiers EN siblings** (⬆ de 0 le 14/07) = 7/7 (↻08-28). Lake =
**recherche** (théorie des nœuds, EPIC #2874). La bilinguisation « in-flight »
signalée dans la version précédente (po-2025 #6429/#6440) est désormais **livrée**.
Les `sorry` résiduels sont des définitions non-définies (`AreMutants`,
`alexanderPolynomial`, `IsSmoothlySlice`, `IsTopologicallySlice`) et des preuves
de transfert classique ouvertes — cibles prover, **pas** un manque i18n. Restant : aucun (7/7 ↻08-28).

### 6. `sensitivity_lean` — EXCELLENT (100 %) ↻08-28

**5 fichiers FR canoniques** (hors lakefile), **5 fichiers EN siblings** = 5/5.
L'état « PARTIEL 67 % » du 07-15 (4 siblings + 6 markers inline bilingues, cas
d'étude Option A vs B) est **supersédé** : l'hybridation a convergé vers le
pattern sibling canonique.

### 7. `conway_lean` — EXCELLENT (82 % nominal, pédagogique 100 %) (gros volume) ↻08-28

**Chemin** : `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/`

**39 fichiers FR canoniques**, **32 fichiers EN siblings** (↻08-28).
~1894 lignes FR canonique (le plus gros contributeur de lignes FR du repo). Lake
= **cœur PEDA Conway** (Life + Doomsday + FRACTRAN + Look-and-Say + Nim + Angel +
**Hashlife**).

**Mantra** : "conway_lean = série Conway hommage (Life + Doomsday + FRACTRAN +
Look-and-Say + Nim + Angel), ~1894 lignes FR canoniques, 4 sorries Hashlife
(cibles prover), 18/27 modules bilingues". Bilinguisation = gros effort, gain
pédagogique élevé (lake le plus visité après `learning_theory_lean`).

**Stratégie recommandée** : poursuivre la bilinguisation par **PR incrémentaux**
sous-série par sous-série. ~~**9 siblings restants** — c'est le principal chantier
i18n substantiel du repo à ce stade.~~ **↻07-17 SUPERSEDÉ** : recompte firsthand =
**26/27 = 96 %**. Les 5 grains type-C propres identifiés le 15/07 (`Doomsday`,
`Fractran`, `FreeWillTheorem`, `LookAndSay`, `Nim`) sont **livrés**. **Les 7 fichiers
sans sibling sont la machinerie prover EN-first recherche** (`HashlifeCorrectness.lean`
7434 lignes, `HashlifeCorrectness/Foundation.lean`, `Walls/{NE,NW,SE,SW}.lean`,
`JumpCapture.lean` — cible prover EPIC #6724 GOL-S4, pas un grain i18n). Le « principal
chantier i18n » conway est **effectivement clos** côté pédagogique.

### 8. `calibration_lean` — EXCELLENT (100 %) ↻08-28

**4 fichiers FR canoniques** (hors lakefile), **4 fichiers EN siblings** = 4/4.
Lake = composant harnais de calibration (déplacé depuis GameTheory, #1764).
L'état « PARTIEL 60 % » du 07-15 (3 siblings + 15 markers inline) est **supersédé**.

### 9. `grothendieck_lean` — EXCELLENT (98 %) ↻08-28

**Chemin** : `MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/`

**60 fichiers FR canoniques**, **59 fichiers EN siblings** (↻08-28 — l'expansion de
l'hommage Grothendieck a plus que doublé le lake depuis le 14/07, et la bilinguisation
a suivi). Lake = **recherche** (EPIC #2159 Grothendieck).
**↻08-28 : les 9 modules type-B EN-canon listés le 15/07** (`CanonicalProps`,
`MathlibMap`, `SheafBasics`, `SheafCohomology/MayerVietoris`, `Sheafification`,
`SieveGenerate`, `SieveLattice`, `SieveOps`, `YonedaLemma`) **ont été flippés et
livrés** — le seul fichier sans sibling est le root agrégateur `Grothendieck.lean`
(type-D, imports-only, sans sibling par convention) : couverture module-level
**59/59 = 100 %**. Le déclassement « FR-flip lourd basse priorité » du 15/07 est
clos.

### 10. `conway_cgt_lean` — FAIT (100 % hors lakefile)

**Chemin** : `MyIA.AI.Notebooks/GameTheory/conway_cgt_lean/`

**1 fichier FR canonique** (hors lakefile), **1 fichier EN sibling** (`CGTTour_en.lean`,
⬆ de 0 le 14/07) = 1/1. L'ancien « candidat PR pilote #1 » est **livré** : le seul
module pédagogique (`CGTTour.lean`) a son sibling EN. Hors `lakefile.lean`
(aglistique), la couverture est complète.

**Mantra** : "conway_cgt_lean = tour pédagogique de la lib CGT de vihdzp
(combinatorial-games), 0 sorry, bilinguisation livrée". ⚠ Build historiquement
dépendant du mismatch mathlib/CombinatorialGames (#6419) — vérifier `lake build`
si modification.

### 11. `finiteness_lean` — BON (50 %) ↻08-28

**2 fichiers FR canoniques** (hors lakefile), 1 fichier EN sibling (`Basic_en.lean`).
Le root `Finiteness.lean` est un agrégateur bilingue inline (Option B historique,
conservé pour la racine — cf. son README).

### 12. `mathlib_examples` — BON (50 %) ↻07-17

2 fichiers FR canoniques, **1 fichier EN sibling** (`Basic_en.lean`, livré #6664
+ root Basic_en #6780). Lake = référence (quelques exemples Mathlib
re-formatés). Seul le root umbrella `MathLibExamples.lean` reste sans sibling
(aglistique). **L'ancien statut « À FAIRE 0 % » est supersédé** — `Basic_en`
est livré.

### 13. Legacy absorbés (`repeated_games_lean`, `social_choice_lean`, `cooperative_games_lean`)

- `repeated_games_lean` (`GameTheory/`) : 1/1 legacy quasi-vide — contenu absorbé
  dans `game_theory_lean` (#6146, cf. #4365).
- `social_choice_lean` (`GameTheory/`) : **disparu du scan** (↻08-28, absorption
  complète, 0 fichier restant — #6040, cf. #4365).
- `cooperative_games_lean` : **plus de `lakefile.lean` standalone** — le lake a
  disparu du scan, contenu migré dans `game_theory_lean/CooperativeGames/` (cf.
  `code-style.md` §Lean, absorption #6274). Ne plus le compter comme lake actif.

### 14. `social_choice_lean_peters` — HORS SCOPE

**1 fichier FR canonique** (hors lakefile), **1 fichier EN sibling**
(`PetersTour_en.lean`, ↻08-28). **Vendored** (lib Peters intégrée, dépendance
Lake). Convention i18n = **hors scope** pour les libs vendored (cf.
`readme-french-first.md` règle périmètre) — un sibling EN du module pédagogique
existe néanmoins désormais.

### 15. Lakes hors scope historique (Probas / Search / Planners / QC / Tweety / SmartContracts)

Voir la table dédiée ci-dessus. Tous déjà à 60-92 % — reste 1-2 siblings de queue
chacun. `decision_theory_lean` (92 %, Probas) et `search_lean` (83 %, Search) sont
les plus avancés ; `erc20_lean` (60 %, SmartContracts) le moins.

---

## Cibles PR pilote (cycles suivants) — révisées 2026-07-15

> **↻07-17 SUPERSEDÉ (po-2024, firsthand disk-recount)** : la table et la
> recommandation ci-dessous datent du 2026-07-15 et sont **largement caduques**.
> (a) La cible #1 `conway_lean` « 5 grains type-C clean » (`Doomsday`,
> `Fractran`, `FreeWillTheorem`, `LookAndSay`, `Nim`) est **ENTIÈREMENT LIVRÉE** —
> recompte = 26/27 = 96 %, seul `HashlifeCorrectness.lean` (3790 L recherche
> EPIC #6724) reste. (b) La « vraie » prochaine cible type-A clean est
> **`lean_game_defs_ext` (0/13)** — lake bayésien FR-canon **manquant de
> l'inventaire 2026-07-15** parce que le script de reproduction (§ « Inventaire
> brut ») ne scanne que `lakefile.lean`, **pas `lakefile.toml`** — blind spot
> TOML. (c) `grothendieck_lean` reste type-B FR-flip recherche (basse priorité),
> inchangé. **Ne pas re-miner conway type-C** (livré) ni mathlib (livré) — voir
> refresh 07-17 en tête de document.

Les cibles #1 (`conway_cgt_lean`) et #3 (`knot_lean`) de la version 14/07 sont
**livrées**. Le reste à faire substantiel se concentre sur les deux gros lakes
recherche et la complétion des queues.

| Priorité | Lake | Reste (par **type de gap**) | Gain pédagogique | Risque |
|---------:|------|-------|------------------|--------|
| **1** | `conway_lean` | **5 grains type-C clean** (bilingue-inline → sibling : `Doomsday`, `Fractran`, `FreeWillTheorem`, `LookAndSay`, `Nim` ; `CollatzLike_en` livré #6663 extract-only) | Très élevé (lake le plus visité après learning_theory) | **Collision** (lane active po-2026 → `[CLAIMED]` **par fichier**) + gros lake, build à vérifier |
| **basse** | `grothendieck_lean` | ~9 substantiels, **tous type-B EN-canon → FR-flip** (pas un gap EN-sibling propre) | Moyen (lake **recherche**, hors priorité francisation pédagogique) | FR-flip lourd + vérifier WIP |
| — | Queues « near-done » | résidus = **umbrellas/lakefiles type-D** (aglistiques), **pas** des gaps substantiels → **effectivement complets** | N/A | N/A |
| basse | `mathlib_examples` | `Basic_en` livré (#6664) ; reste = contenu FR quasi-nul type-D | Faible | Faible |

> **Note post-recompte (2026-07-15)** : `erc20_lean` passe 3→4 EN siblings (`ERC20_en`
> livré #6662, glob lakefile mis à jour) ; `mathlib_examples` 0→1 (`Basic_en` #6664) ;
> `conway_lean` +1 (`CollatzLike_en` #6663). Ces trois lakes ne sont plus des cibles
> pilote « à 0 ».

**Recommandation révisée c.515+ (audit firsthand exhaustif conway)** : `conway_lean`
(cible #1) offre **5 grains type-C clean**. Les 6 fichiers non-Life sont bilingue-inline,
donc sous le greenlight option-c #4980 (Option B rejetée) chacun est une conversion
sibling propre : créer `Foo_en.lean` EN-seul **et** retirer le bloc EN de la base
(→ FR-seule, pattern `Angel.lean`). Restent 5 après `CollatzLike_en` (#6663, extract-only) :
`Doomsday`, `Fractran`, `FreeWillTheorem`, `LookAndSay`, `Nim`. C'est la **lane active de
po-2026** → `[CLAIMED]` **par fichier** (dédup R3), **pas** un motif de pivot.
`grothendieck_lean` est déclassé en **priorité basse** (type-B FR-flip, recherche, hors
priorité francisation pédagogique). **Conséquence coordination** : un worker sur la lane
conway **continue conway** ; le pivot cross-lane (pool global `gh issue list --state open`)
ne s'active **qu'après** épuisement des 5 grains conway — jamais en invoquant une
« saturation » que cet audit réfute.

---

## Inventaire brut — sortie reproductible

Commande de reproduction (à exécuter depuis la racine du dépôt). Le périmètre de
scan a été **élargi 2026-07-15** pour couvrir tous les lakes Lean du repo (Probas,
Search, Planners, QC, Tweety, SmartContracts en plus du scope historique) :

```bash
for lake in \
    MyIA.AI.Notebooks/SymbolicAI/Lean/*/ MyIA.AI.Notebooks/GameTheory/*/ \
    MyIA.AI.Notebooks/ML/*/ MyIA.AI.Notebooks/Sudoku/*/ \
    MyIA.AI.Notebooks/Probas/*/ MyIA.AI.Notebooks/Search/*/ \
    MyIA.AI.Notebooks/SymbolicAI/Planners/*/ MyIA.AI.Notebooks/SymbolicAI/SmartContracts/*/ \
    MyIA.AI.Notebooks/SymbolicAI/Tweety/*/ MyIA.AI.Notebooks/QuantConnect/*/; do
  # ↻07-17 : accepter lakefile.lean ET lakefile.toml (sinon lakes TOML comme
  # lean_game_defs_ext sont invisibles au scan → inventaire incomplet)
  if [ -f "$lake/lakefile.lean" ] || [ -f "$lake/lakefile.toml" ]; then
    lake_name=$(basename "$lake")
    fr=$(find "$lake" -name '*.lean' -not -path '*.lake*' -not -name '*_en.lean' -not -name 'lakefile.lean' 2>/dev/null | wc -l)
    en=$(find "$lake" -name '*_en.lean' -not -path '*.lake*' 2>/dev/null | wc -l)
    echo "$lake_name: fr_files=$fr en_files=$en"
  fi
done | sort
```

Sortie 2026-07-15 (refresh ai-01, `origin/main` @ `77294f5941`) :

```
argumentation_lean: fr_files=7 en_files=5
calibration_lean: fr_files=5 en_files=3
conway_cgt_lean: fr_files=2 en_files=1
conway_lean: fr_files=28 en_files=18
decision_theory_lean: fr_files=13 en_files=12
erc20_lean: fr_files=5 en_files=3
finiteness_lean: fr_files=3 en_files=1
game_theory_lean: fr_files=26 en_files=21
grothendieck_lean: fr_files=26 en_files=15
kelly_lean: fr_files=4 en_files=3
knot_lean: fr_files=8 en_files=6
learning_theory_lean: fr_files=19 en_files=18
mathlib_examples: fr_files=3 en_files=0
minimax_lean: fr_files=5 en_files=4
planning_lean: fr_files=4 en_files=3
repeated_games_lean: fr_files=1 en_files=1
search_lean: fr_files=6 en_files=5
sensitivity_lean: fr_files=6 en_files=4
social_choice_lean: fr_files=1 en_files=0
social_choice_lean_peters: fr_files=2 en_files=0
sudoku_lean: fr_files=5 en_files=4
```

> Delta vs epoch 2026-07-14 (`455492afa`) : `knot_lean` 8/0 → 8/6 (po-2025
> #6429/#6440) ; `conway_cgt_lean` 2/0 → 2/1 (CGTTour_en) ; `conway_lean` 28/11 →
> 28/18 ; `grothendieck_lean` 26/12 → 26/15 ; `game_theory_lean` 26/19 → 26/21 ;
> `cooperative_games_lean` disparu du scan (absorption complète, plus de lakefile).
> Nouveaux lakes désormais suivis (élargissement scope) : `decision_theory_lean`,
> `search_lean`, `planning_lean`, `kelly_lean`, `argumentation_lean`, `erc20_lean`.

Sortie 2026-08-28 (refresh po-2024, `origin/main` @ `c9811ce1ff`, See #13211) :

```
argumentation_lean: fr_files=6 en_files=5
assignment_lean: fr_files=5 en_files=5
asymmetric_information_lean: fr_files=6 en_files=6
calibration_lean: fr_files=4 en_files=4
conway_cgt_lean: fr_files=1 en_files=1
conway_lean: fr_files=39 en_files=32
decision_theory_lean: fr_files=13 en_files=13
erc20_lean: fr_files=4 en_files=4
finiteness_lean: fr_files=2 en_files=1
galois_lean: fr_files=2 en_files=0
game_theory_lean: fr_files=28 en_files=21
grothendieck_lean: fr_files=60 en_files=59
kelly_lean: fr_files=3 en_files=3
knot_lean: fr_files=7 en_files=7
lean_game_defs: fr_files=6 en_files=6
lean_game_defs_ext: fr_files=13 en_files=13
learning_theory_lean: fr_files=18 en_files=18
mathlib_examples: fr_files=2 en_files=1
mimo_lean: fr_files=6 en_files=6
minimax_lean: fr_files=4 en_files=4
planning_lean: fr_files=3 en_files=3
repeated_games_lean: fr_files=0 en_files=0
search_lean: fr_files=5 en_files=5
sensitivity_lean: fr_files=5 en_files=5
social_choice_lean_peters: fr_files=1 en_files=1
sudoku_lean: fr_files=4 en_files=4
```

> Delta vs 07-15 : `lean_game_defs_ext` 13/0 → 13/13 (grain type-C livré) ;
> `grothendieck_lean` 26/15 → 60/59 (expansion hommage + FR-flips type-B livrés) ;
> `conway_lean` 28/18 → 39/32 (machinerie prover b3'/c.95/c.1035 ajoutée, EN-less
> by design ; pédagogique complet) ; `decision_theory_lean` 13/12 → 13/13 ;
> `search_lean` 6/5 → 5/5 ; `planning_lean` 4/3 → 3/3 ; `kelly_lean` 4/3 → 3/3 ;
> `erc20_lean` 5/3 → 4/4 ; `argumentation_lean` 7/5 → 6/5 ; `conway_cgt_lean`
> 2/1 → 1/1 ; `social_choice_lean` disparu (0 fichier) ;
> `social_choice_lean_peters` 2/0 → 1/1 (`PetersTour_en.lean`). Nouveaux lakes
> suivis : `assignment_lean`, `asymmetric_information_lean`, `galois_lean`,
> `mimo_lean`.

---

## Voir aussi

- [LEAN_INVENTORY.md](LEAN_INVENTORY.md) — inventaire sorry/modules par lake (même registre)
- [GameTheory/LEAN_INVENTORY.md](../../GameTheory/LEAN_INVENTORY.md) — version GameTheory
- Issue [#4980](https://github.com/jsboige/CoursIA/issues/4980) — parente (open, tranche 1/3)
- Issue [#1650](https://github.com/jsboige/CoursIA/issues/1650) — EPIC traduction multilingue
- [`readme-french-first.md`](../../.claude/rules/readme-french-first.md) — convention sister `README.en.md`
- PR #6048 (c.356 RepeatedGames root bilingue FR+EN) — convention ratifiée
- PR #6040 (c.357 Lean regroupement SocialChoice) — multi-lib lean_lib pattern
