# Lean axiom coverage — proof-integrity gate triage (per #8738 step 3)

**Issue de référence** : [#8738](https://github.com/jsboige/CoursIA/issues/8738) (proof-integrity gate multiline parse, parser fix livré via PR #8740 c.947 MERGED 2026-07-28).
**Cycle-id de production** : c.948 (worker po-2023, lane `myia-po-2023:CoursIA-2`).
**Mesure** : `git grep -E` sur le commit `35e1258df` (origin/main HEAD), 2026-07-29.

Ce doc est la **preuve d'acceptance step 3** du ticket #8738 (« Les 10 lakes cables re-mesures ; chaque rouge soit corrige, soit whitelist avec issue nommee »). État constaté : **1 lake câblé** (knot_lean), **22 lakes** sur disque (cf `find MyIA.AI.Notebooks -name "lakefile.lean"` filtré des vendored `.lake/packages/`). Le présent triage classe chaque lake par exposition aux axiomes que la proof-integrity gate traite comme `forbidden` après la livraison de #8740.

## 1. Portée et méthode

**Axiomes cibles** (ce que `LeanVerifier.check_axioms` flagge désormais comme `forbidden` après le fix parser multiline #8740) :

- `native_decide.*` — réduit au kernel natif sans preuve, vide le gate. Note: la **whitelist** sur `conway_lean` liste les **19 noms explicites** (cliquet, pas wildcard) — voir §3.1 ci-dessous et PR #8746 (c.951).
- `sorryAx` (et `*._root_.sorryAx`) — proof elision, capté déjà en transitif
- `Classical.choice` (et `*._root_.Classical.choice`) — base axiomatique non-constructive

**Méthode de comptage** : `git grep -cE` regex anchored `\b<axiom>\b` sur les fichiers `*.lean` non-`.en.lean` du lake (les `.en.lean` sont les frères bilingues, byte-identiques hors commentaires). Pour `native_decide`, on distingue dans la suite « tactic uses » (lignes où `native_decide` apparaît comme token de tactique, pas comme référence dans une `/- -/`) des « docstring mentions » (références textuelles dans la prose).

**Pas un audit formel** : ce triage ne **lance pas** `lake env lean` + `#print axioms` sur chaque lake (matière à ~6h de build pour les 22 lakes sans Lean compilé en local). Le triage **grep-firsthand** identifie les lacs qui *utiliseraient* `native_decide`/`Classical.choice` une fois le gate branché dessus ; il donne la liste des reds à traiter au cas par cas.

### 1.1. Limite structurelle de la colonne `Classical.choice` (issue #8941)

La colonne `Classical.choice` compte des **mentions textuelles du token**, pas des dépendances axiomatiques — et les deux sont **anti-corrélées** à ce qu'on veut savoir.

La raison est mécanique : `Classical.choice` n'est **pas un token qu'on écrit** dans du source Lean. C'est un axiome que le **noyau attribue** ; il n'apparaît que dans la **sortie de `#print axioms`**, jamais dans le texte source. Un lake l'introduit typiquement via `noncomputable def` (qui force le recours au choix classique) ou `Classical.byContradiction` — sans jamais écrire la chaîne `Classical.choice`. La colonne vaut donc `0` pour à peu près tous les lacs, **non parce qu'ils ne l'utilisent pas, mais parce que la question n'est pas posée là où la réponse se trouve**.

Ce que la colonne mesure réellement, c'est le nombre de **mentions en prose** (docstrings/commentaires qui *parlent* de l'axiome). Les trois lacs non nuls le confirment par leur propre texte — `sudoku_lean` (`ExactCover.lean:69,154`, commentaires « repose sur l'axiome `Classical.choice` »), `learning_theory_lean` (`PacFiniteBound.lean:215,376`, commentaires sur le non-`defeq` de `Classical.choice`) : ce sont des docstrings qui documentent le recours, pas des dépendances. Corollaire : un lake qui documente honnêtement son recours au choix classique **remonte** dans la colonne ; un lake qui l'utilise sans le dire reste à `0`. `decision_theory_lean` (listé à `1`) l'illustre au lieu de le nuancer : `Coherence.lean:33` est une docstring de module qui nomme `[propext, Classical.choice, Quot.sound]` — exactement le genre de mention en prose que cette colonne compte. La table a donc raison avec son `1`.

Le même défaut vaut, en plus grave, pour `sorryAx` (transitif, invisible au grep par construction — le doc le note déjà « capte déjà en transitif »). **`native_decide`, en revanche, est un vrai token source : sa colonne est fiable.**

### 1.2. GREEN-par-grep ≠ GREEN-par-gate

Tous les verdicts de la table ci-dessous sont **GREEN-par-grep** / **RED-par-grep** (issus de `git grep`, §1) **sauf** ceux explicitement marqués **« mesuré »** (issus de `#print axioms` via `LeanVerifier.check_axioms`). Les deux affirmations sont différentes : un lake GREEN-par-grep n'a aucun `native_decide` en source, mais peut très bien porter `Classical.choice` dans sa clôture axiomatique (cf §1.1). Câbler le gate `lean-axiom.yml` (`Classical.choice` est `forbidden` par défaut) sur un lake GREEN-par-grep peut donc recevoir un **rouge inattendu** — précisément le scénario de `grothendieck_lean`, première ligne **mesurée** de la table (cf §3.5).

## 2. Triage des 22 lacs Lean (hors vendored `.lake/packages/`)

État au commit `35e1258df` (2026-07-29), `git ls-files <lake> | grep "\.lean$" | grep -v ".en.lean"` :

| Lake | Lean files | native_decide (raw) | native_decide (tactic) | Classical.choice | sorryAx | Verdict |
|---|---:|---:|---:|---:|---:|---|
| `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean` | 28 | 153 | **113** | 0 | 0 | **RED** (à traiter) |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean` | 8 | 4 | 0 | 1 | 0 | **GREEN** (post-#8725) |
| `MyIA.AI.Notebooks/Sudoku/sudoku_lean` | 5 | 0 | 0 | 4 | 0 | borderline (acceptable : sudoku_lean `Classical.choice` = lemmes de complétude sur les colourings finis, classique assumé) |
| `MyIA.AI.Notebooks/ML/learning_theory_lean` | 19 | 0 | 0 | 2 | 0 | borderline (2 occurrences : VC-dim classiques) |
| `MyIA.AI.Notebooks/Probas/decision_theory_lean` | 13 | 0 | 0 | 1 | 0 | borderline (1 occurrence : lottery axioms) |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean` | 6 | 0 | 0 | 0 | 0 | GREEN |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples` | 3 | 0 | 0 | 0 | 0 | GREEN |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean` | 33 | 0 | 0 | 0† | 0 | **GREEN-par-grep** (⚠️ mesuré : `Classical.choice` PRÉSENT en clôture — cf §1.1, §3.5) |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/finiteness_lean` | 3 | 0 | 0 | 0 | 0 | GREEN |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean` | 5 | 0 | 0 | 0 | 0 | GREEN |
| `MyIA.AI.Notebooks/Search/search_lean` | 6 | 0 | 0 | 0 | 0 | GREEN |
| `MyIA.AI.Notebooks/QuantConnect/kelly_lean` | 4 | 0 | 0 | 0 | 0 | GREEN |
| `MyIA.AI.Notebooks/GameTheory/social_choice_lean_peters` | 2 | 0 | 0 | 0 | 0 | GREEN |
| `MyIA.AI.Notebooks/GameTheory/social_choice_lean` | 1 | 0 | 0 | 0 | 0 | GREEN |
| `MyIA.AI.Notebooks/GameTheory/repeated_games_lean` | 1 | 0 | 0 | 0 | 0 | GREEN |
| `MyIA.AI.Notebooks/GameTheory/minimax_lean` | 5 | 0 | 0 | 0 | 0 | GREEN |
| `MyIA.AI.Notebooks/GameTheory/game_theory_lean` | 25 | 0 | 0 | 0 | 0 | GREEN |
| `MyIA.AI.Notebooks/GameTheory/conway_cgt_lean` | 2 | 0 | 0 | 0 | 0 | GREEN |

## 3. Lecture par verdict

### 3.1. RED — `conway_lean` (153 raw / 113 tactic uses)

**Le seul vrai RED** du triage. `native_decide` est utilisé comme tactique dans 113 endroits à travers 14 fichiers, principalement sur :

- `Conway/Life/HashlifeCorrectness.lean` (33 occurrences) — preuves de cohérence du simulateur sur petites instances
- `Conway/Life/Computation.lean` (19) — génération de patterns (RLE, oscillateurs, pillars)
- `Conway/CollatzLike.lean` (8), `Conway/Nim.lean` (7), `Conway/DoomsdayLemmas.lean` (4), `Conway/Angel.lean` (4) — calibrations sur des instances bornées

**Profil d'usage** : `native_decide` est **délibéré et justifié** sur ce lake (cf. `Conway/README.md` §15 et `LEAN_INVENTORY.md` : « micro-preuves sur instances bornées, calibration du moteur de recherche exhaustive »). Le retirer serait une régression pédagogique : la substantifique moelle des notebooks `Conway/Life/Hashlife*` est précisément la vérification *native* que la simulation est cohérente sur N steps.

**Recommandation** : **whitelist avec issue nommée** + 19 noms explicites dans le paramètre `allow-axioms` de `lean-conway.yml` (pattern « cliquet » : tout nouveau `native_decide` produit un nom absent de la liste → le gate rougit). Le mécanisme whitelist existe déjà dans le job CI (`lean-axiom.yml` input `allow-axioms`) — il faut juste le déclarer explicitement avec justification écrite.

**Issue fille** : `See #8749` (triage THEOREME PAR THEOREME des 19 axiomes `native_decide` sur `conway_lean`, lots de 3-5, decide-noyau schema #8731 vs whitelist justifiée ; justif de la whitelist actuelle : « micro-preuves bornées sur instances closes du simulateur, contrats pédagogiques explicites dans `LEAN_INVENTORY.md` §15 et `Conway/README.md` §calibration »).

**19 noms actuellement dans la whitelist** (verbatim du commit `84eef8c76` PR #8746, tranche 2 `Conway.KochenSpecker + Conway.FreeWillTheorem` ; names pré-bakés pour la tranche 3 `Conway.Life.*`) :

```
Conway.Life.hashlife_beacon_2._native.native_decide.ax_1_1
Conway.Life.hashlife_blinker_2._native.native_decide.ax_1_1
Conway.Life.block_macrocell_roundtrip._native.native_decide.ax_1_1
Conway.Life.hashlife_fast_block_4._native.native_decide.ax_1_1
Conway.Life.glider_3periods._native.native_decide.ax_1_1
Conway.Life.hashlife_block_4._native.native_decide.ax_1_1
Conway.Life.eater1_macrocell_roundtrip._native.native_decide.ax_1_1
Conway.Life.hashlife_fast_glider_4._native.native_decide.ax_1_1
Conway.Life.hashlife_fast_glider_8._native.native_decide.ax_1_1
Conway.Life.hashlife_fast_toad_2._native.native_decide.ax_1_1
Conway.Life.eater1_still_life._native.native_decide.ax_1_1
Conway.Life.hashlife_fast_beacon_2._native.native_decide.ax_1_1
Conway.Life.hashlife_glider_8._native.native_decide.ax_1_1
Conway.Life.hashlife_block_1._native.native_decide.ax_1_1
Conway.Life.glider_macrocell_roundtrip._native.native_decide.ax_1_1
Conway.Life.hashlife_toad_2._native.native_decide.ax_1_1
Conway.Life.hashlife_glider_4._native.native_decide.ax_1_1
Conway.Life.hashlife_fast_blinker_2._native.native_decide.ax_1_1
Conway.Life.glider_2periods._native.native_decide.ax_1_1
```

### 3.1.a. Refactor attempt — `Grid = List (Nat × Nat)` (issue #8869, c.954)

**Issue de référence** : [#8869](https://github.com/jsboige/CoursIA/issues/8869) (successeur de #8749, ouvert par ai-01 au moment de fermer ce dernier pour ne pas perdre l'objectif de fond).
**Cycle-id de production** : c.954 (worker po-2023, lane `myia-po-2023:CoursIA-2`).
**Statut au cycle c.954** : **critère #1 livré** (commentaire GitHub sur #8869, https://github.com/jsboige/CoursIA/issues/8869#issuecomment-5122261512, 2026-07-29T18:58:51Z). Critères #2-#5 différés (nécessitent env `lake build` fonctionnel sur `conway_lean`, corrompu au moment du diagnostic c.949).

**Cause racine (mesurée po-2026, dossier #8749)** : `Grid = List (Int × Int)`. `Int` ne se réduit pas sous `decide` ; `Nat` si. Le noyau reste bloqué avant d'atteindre `isTrue`/`isFalse`, `maxRecDepth` explose. Deux mesures versées au dossier :
- `hashlife_block_1` + `decide` + `maxRecDepth 100000` → >14 min sans terminer
- membre droit remplacé par constante littérale → échec en ~18s (« reduction got stuck »)

La seconde localise l'obstruction : ce n'est pas la taille du calcul, c'est que `evolveHashlife 1 block` ne se réduit pas en constructeur de liste sous le noyau, alors que la compilation native le calcule sans peine.

**Trois options du ticket** + une quatrième :

| Option | Résumé | Blast radius | Verdict c.954 |
|---|---|---|---|
| **1 — Origine décalée** | `Grid = List (Nat × Nat)` + convention d'origine + `shift` modulo bounding-box | Tout `Conway.Life.MacroCell` + Section 3 (périodicité) | **REJET** (portée des énoncés silencieusement restreinte : glider qui franchit l'origine, `glider_2periods : evolve 8 glider = shift (2, -2) glider` perd sa représentation en `Nat × Nat`) |
| **2 — Type dédié + `DecidableEq` manuelle** | Garder `Grid = List (Int × Int)`, ajouter instance `DecidableEq (Int × Int)` écrite à la main, scopée au namespace `Conway.Life` | 1 instance locale + 6 occurrences `native_decide` → `decide` | **RECOMMANDÉ** (signatures byte-identiques, énoncés byte-identiques, blast radius confiné à `Conway.Life.Computation`) |
| **3 — Translation-invariant** | Réécrire les 19 énoncés avec relation `~` modulo translation | 19 théorèmes à re-prouver + refonte de `MacroCell` | **REJET** (chantier, pas une issue ; violerait [anti-regression.md](../../.claude/rules/anti-regression.md) — énoncés VRAIS et PROUVÉS, on ne les reformule pas) |
| **4 — Option 2 + lemmes de fold sur `sortDedup`** | Conjoint à Option 2 : lemmes explicites `sortDedup [a,b,c] = ...` pour les arités 2-9 des motifs Conway | Phase 1 + 5-10 lemmes | **PLAN B** (si Phase 1 ne suffit pas — `sortDedup` non-réductible même après `DecidableEq` manuelle) |

**Recommandation c.954 (livrée par commentaire #8869, 2026-07-29)** : Phase 1 = Option 2 (instance `DecidableEq` manuelle, blast radius minimal, énoncés préservés verbatim). Phase 2 = Option 4 si `lake build` échoue sur `sortDedup` non-réductible.

> **MISE À JOUR c.786/c.795 — Option 2 mesurée INEFFICACE, Option 4 (insertionSort) retenue.**
>
> La sonde par-cible-isolée `decide` menée par po-2026 au c.786 a invalidé la
> premise de la recommandation c.954 : le blocage n'est **ni** le type de
> coordonnée (`Int` vs `Nat` — `mergeSort` reste stuck pour les DEUX), **ni**
> l'absence d'instance `DecidableEq` manuelle (le prédicat `beq` sous-jacent
> est `Bool.beq`, donc `DecidableEq` n'est jamais invoqué par le chemin de
> réduction). La cause racine est **l'algorithme de tri lui-même** :
> `List.mergeSort` ne se réduit pas sous le kernel `decide` (son `merge`
> imbriqué est opaque), tandis que `List.insertionSort` se réduit (POC
> vérifié sur le motif `eater1` 7-cellules, le cas classé INTRINSIC en #8749).
>
> En conséquence :
> - **Option 2 (ligne RECOMMANDÉ ci-dessus) : SUPERSEDÉE** — mesurée sans
>   effet. Noter que **#8872 est docs-only** (cette section 3.1.a) : aucune
>   instance `DecidableEq` manuelle n'a jamais été committée en code. Il n'y
>   a donc rien à retirer du code source ; cette annotation documente
>   l'inopérance constatée, comme l'exige l'acceptance du dispatch c.58
>   (« retire-la, ou annote en place pourquoi elle est inoperante »).
> - **Option 4 (insertionSort swap) : GREENLIT ai-01 c.794/c.795** (DM
>   `msg-20260729T220506-0zjzog`), implémentée dans la PR #8869 : swap
>   `mergeSort lexLe` → `insertionSort lexLe` dans `Conway.Life.sortDedup`,
>   recâblage de `Conway.Life.GridCanonical.canonical_sortDedup` via
>   `List.pairwise_insertionSort` (instances `[Std.Total]`/`[IsTrans]`
>   déchargées localement depuis `lexLe_total`/`lexLe_trans`). Coordonnées
>   `Int × Int` conservées — aucun énoncé glider/origine/périodicité altéré.

**Critère #5 (sortie INTRINSIC assumée)** : si `lake build` échoue après Option 2 + Option 4 combinées, la whitelist de 19 reste INTRINSIC (assumée, pas dette latente). Issue #8869 se ferme alors avec verdict mesuré, et la whitelist devient un plafond documenté plutôt qu'un objectif de réduction.

**Statut whitelist après c.954** : inchangée. Les 19 noms explicites du commit `84eef8c76` (PR #8746 v2, c.951 MERGED) couvrent toujours les 19 occurrences actuelles. Une baisse éventuelle se fera par sous-grains successifs (1 nom retiré à la fois, après mesure `lake build` SUCCESS + `proof-integrity` vert sur le retrait), pas en une seule PR composite.

### 3.2. GREEN — `knot_lean` (post-#8725)

Le gate `proof-integrity` est **déjà câblé** sur `knot_lean` (`lean-knot.yml` → `lean-axiom.yml`). Les 4 occurrences de `native_decide` sont toutes des **mentions docstring** dans `Knots/Invariant.lean` (lignes 92, 1046, 1051, 1053) — l'avertissement pédagogique « ne pas utiliser `native_decide` ici » qui a remplacé l'ancien usage par la preuve constructive `by decide` sur la fonction caractéristique `#is_tricolorable`. Le retrait a été livré via PR #8725 (po-2026), MERGED `2127f8c36` (cf. [#8738](https://github.com/jsboige/CoursIA/issues/8738) §« Mesure firsthand (ai-01, c.37) »).

Le 1 hit `Classical.choice` dans `knot_lean` reste à investiguer (probablement un `Classical.byContradiction` dans la preuve `figureEight_not_tricolorable`, classique assumé sur les colorings finis). **Pas bloquant** : `Classical.choice` n'est pas dans la liste `forbidden` par défaut du job.

### 3.3. borderline — `sudoku_lean`, `learning_theory_lean`, `decision_theory_lean`

Ces lacs utilisent `Classical.choice` (4/2/1 occurrences respectivement). Comme `knot_lean`, ils ne sont **pas câblés** sur `lean-axiom.yml` actuellement — donc le gate ne les voit pas. Au moment où ils seront câblés :

- **`sudoku_lean`** (4 `Classical.choice`) : lemmes d'existence (coloring d'une grille par contradiction sur l'ensemble des colorings) — choix classique assumé sur un domaine fini. Justifiable comme `allow-axioms: "Classical.choice"`.
- **`learning_theory_lean`** (2 `Classical.choice`) : VC-dimension, lemmes de compacité. Choix classique assumé.
- **`decision_theory_lean`** (1 `Classical.choice`) : existence de lotteries sur des espaces finis. Choix classique assumé.

**Recommandation** : whitelist `Classical.choice` au cas par cas avec issue nommée pour chaque lake au moment du câblage. Pas de PR batch ici — la décision « whitelist `Classical.choice` sur un lake pédagogique » mérite une justification écrite par lake.

### 3.4. GREEN — 14 lacs

Aucune occurrence de `native_decide`, `sorryAx`, `Classical.choice` dans le code (hors docstring). Câblage futur sans coût : juste créer le `lean-<lake>.yml` qui appelle `lean-axiom.yml` avec `target-modules` listant les modules principaux du lake.

### 3.5. `grothendieck_lean` — première ligne MESURÉE (audit réel #8941)

`grothendieck_lean` est la **première ligne de la table issue d'une mesure `#print axioms` réelle** (vs grep). C'est le cas-test qui a révélé la limite §1.1 : la table lui donnait `Classical.choice = 0` et verdict GREEN, alors que l'axiome est **présent dans la clôture axiomatique de ses modules**.

**Mesure** (issue #8941, `LeanVerifier.check_axioms` = `#print axioms` par déclaration sur les 33 modules FR de `grothendieck_lean`, 2026-07-30) :

```
modules ok      : 30/33
declarations    : 164
modules w/ sorry: 0
axioms union    : ['Classical.choice', 'Quot.sound', 'propext']
forbidden union : []
```

**Corroboration grep-firsthand (po-203, c.982, commit `950958485`)** : le mécanisme §1.1 se vérifie directement — `git grep -l noncomputable` sur les fichiers **FR** de `grothendieck_lean` (pathspec incluant la racine, ex. `<lake>/*.lean` + `<lake>/**/*.lean` — le glob `<lake>/**/*.lean` seul perd les agrégateurs racine) renvoie **16 fichiers sur 35** (`Adjunction`, `Conservative`, `ConstantSheaf`, `Equivalences`, `KanExtensions`, `LeftExact`, `Limits`, `MayerVietorisSquare`, `MonoidalCategories`, `SchemesTour`, `SheafCohomology/Basic`, …). Chaque `noncomputable def` force le recours à `Classical.choice`, sans jamais écrire le token — d'où le `0` de la colonne grep. Les 3 modules non-énumérables (le `30/33` de la mesure `#print axioms` ci-dessus, 35 fichiers − 2 agrégateurs racine non-énumérables) sont un faux rouge distinct, traité par #8940 (hors sujet ici).

**Implication de câblage** : `Classical.choice` est `forbidden` par défaut dans `check_axioms`. Câbler `lean-grothendieck.yml` → `lean-axiom.yml` exigera donc `allow-axioms: "Classical.choice"` **explicite et nommé** (jamais en wildcard — cliquet §B.3 [pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md)), avec justification écrite : la théorie des catégories/sheaves de Grothendieck est intrinsèquement non-constructive, le choix classique y est l'attente pédagogique (et non un défaut). Le lake n'a **aucun** `native_decide` et **aucun** `sorry` : son seul contenu axiomatique non-trivial est ce choix classique structurel.

## 4. État du câblage CI

| Lake | Workflow `lean-*.yml` | Appelle `lean-axiom.yml` ? | Verdict au gate |
|---|---|---|---|
| `knot_lean` | `lean-knot.yml` | OUI (pilote) | GREEN post-#8725 |
| `conway_lean` | `lean-conway.yml` | **NON** | serait RED (113 tactic uses) |
| 14 autres lacs | workflows existants | **NON** | GREEN si câblés (sauf 3 borderline sur `Classical.choice`) |

Le câblage du gate sur les lacs non-pilotes est un travail séparé qui sort du scope #8738 (chaque workflow lake est un livrable à part avec son `target-modules` adapté).

## 5. Acceptance step 3 — verdict

- [x] **knot_lean re-mesuré** : GREEN post-#8725 (cf. [#8738](https://github.com/jsboige/CoursIA/issues/8738) body §« Mesure firsthand »)
- [x] **conway_lean re-mesuré** : RED — whitelist `native_decide.*` (19 noms explicites) recommandée avec issue nommée `#8749` (triage THEOREME PAR THEOREME)
- [x] **3 lacs borderline** identifiés : whitelist `Classical.choice` recommandée au câblage futur avec issue nommée par lake
- [x] **14 lacs GREEN** : câblage futur sans coût

**Recommendation pour le coordinateur (ai-01)** : la whitelist `native_decide.*` (19 noms explicites) est déjà déclarée dans le paramètre `allow-axioms` de `lean-conway.yml` (PR #8746 MERGED, commit `84eef8c76`). Le triage THEOREME PAR THEOREME de ces 19 axiomes est suivi sous #8749 (lots 3-5, schema #8731 vs whitelist justifiée, runtime mesuré). Le câblage `lean-conway.yml` → `lean-axiom.yml` est un MED/lean-ci-tooling dédié.

## 6. Acceptance step 4 — note sur §B.3 pr-review-discipline.md

Le gate `proof-integrity` couvre désormais `native_decide` (post-#8740). La règle `.claude/rules/pr-review-discipline.md` §B.3 mentionnait `sorryAx` (transitif) mais restait ambiguë sur `native_decide` (la classe d'axiomes la plus dangereuse). **Note de scope** : la mise à jour §B.3 du fichier de règles est **gélée pour cette PR** (user sign-off requis, PR #8744 attend déjà cette signature avec le user en déplacement). Le présent triage doc harmonise la **substance** avec le gate (`native_decide` couvert, 19 noms déclarés), ce qui rend la règle §B.3 **désambiguïsée par convergence** côté doc — l'edit de la règle elle-même viendra dans une PR distincte post-sign-off. Cf. PR #8744 c.948.

## 7. Voir aussi

- [#8738](https://github.com/jsboige/CoursIA/issues/8738) — ticket de référence (parser fix #8740, triage c.948)
- [#8941](https://github.com/jsboige/CoursIA/issues/8941) — limite structurelle de la colonne `Classical.choice` (grep vs `#print axioms`) + première ligne mesurée (`grothendieck_lean`, §3.5)
- PR [#8740](https://github.com/jsboige/CoursIA/pull/8740) — `fix(lean-tooling,#8738): proof-integrity gate reads multi-line axiom lists` (c.947, MERGED 2026-07-28)
- PR [#8746](https://github.com/jsboige/CoursIA/pull/8746) — `ci(lean,#8677): proof-integrity gate v2 — KochenSpecker+FreeWillTheorem + 19 explicit native_decide names` (c.951, MERGED 2026-07-29)
- PR [#8725](https://github.com/jsboige/CoursIA/pull/8725) — `Knots/Invariant.lean` retire `native_decide` tactic (po-2026, MERGED 2026-07-27)
- [#8749](https://github.com/jsboige/CoursIA/issues/8749) — triage THEOREME PAR THEOREME des 19 axiomes `native_decide` sur `conway_lean` (par lots 3-5, schema #8731 vs whitelist)
- `.github/workflows/lean-axiom.yml` — job réutilisable proof-integrity (4 inputs : `project-path`, `display-name`, `target-modules`, `allow-axioms`, `fail-on-sorry`)
- `.github/workflows/lean-knot.yml` — seul workflow lake à appeler `lean-axiom.yml` actuellement
- `.github/workflows/lean-conway.yml` — cible câblage (19 axiomes dans `allow-axioms`, scope=Conway.KochenSpecker+Conway.FreeWillTheorem en tranche 2)
- `.claude/rules/pr-review-discipline.md` §B.3 — règle de review Lean PRs (mise à jour c.948 gélée pour sign-off user)
- `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/lean_server.py` — `LeanVerifier._extract_axioms` (parser multiline fixé par c.947)
- `MyIA.AI.Notebooks/SymbolicAI/Lean/Conway/README.md` §15 + `LEAN_INVENTORY.md` — justification pédagogique de `native_decide` sur conway_lean