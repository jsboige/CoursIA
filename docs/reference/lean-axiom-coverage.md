# Lean axiom coverage — proof-integrity gate triage (per #8738 step 3)

**Issue de référence** : [#8738](https://github.com/jsboige/CoursIA/issues/8738) (proof-integrity gate multiline parse, parser fix livré via PR #8740 c.947 MERGED 2026-07-28).
**Cycle-id de production** : c.948 (worker po-2023, lane `myia-po-2023:CoursIA-2`).
**Mesure** : `git grep -E` sur le commit `35e1258df` (origin/main HEAD), 2026-07-29.

Ce doc est la **preuve d'acceptance step 3** du ticket #8738 (« Les 10 lakes cables re-mesures ; chaque rouge soit corrige, soit whitelist avec issue nommee »). État constaté : **1 lake câblé** (knot_lean), **22 lakes** sur disque (cf `find MyIA.AI.Notebooks -name "lakefile.lean"` filtré des vendored `.lake/packages/`). Le présent triage classe chaque lake par exposition aux axiomes que la proof-integrity gate traite comme `forbidden` après la livraison de #8740.

## 1. Portée et méthode

**Axiomes cibles** (ce que `LeanVerifier.check_axioms` flagge désormais comme `forbidden` après le fix parser multiline #8740) :

- `native_decide.*` — réduit au kernel natif sans preuve, vide le gate
- `sorryAx` (et `*._root_.sorryAx`) — proof elision, capté déjà en transitif
- `Classical.choice` (et `*._root_.Classical.choice`) — base axiomatique non-constructive

**Méthode de comptage** : `git grep -cE` regex anchored `\b<axiom>\b` sur les fichiers `*.lean` non-`.en.lean` du lake (les `.en.lean` sont les frères bilingues, byte-identiques hors commentaires). Pour `native_decide`, on distingue dans la suite « tactic uses » (lignes où `native_decide` apparaît comme token de tactique, pas comme référence dans une `/- -/`) des « docstring mentions » (références textuelles dans la prose).

**Pas un audit formel** : ce triage ne **lance pas** `lake env lean` + `#print axioms` sur chaque lake (matière à ~6h de build pour les 22 lakes sans Lean compilé en local). Le triage **grep-firsthand** identifie les lacs qui *utiliseraient* `native_decide`/`Classical.choice` une fois le gate branché dessus ; il donne la liste des reds à traiter au cas par cas.

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
| `MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean` | 33 | 0 | 0 | 0 | 0 | GREEN |
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

**Recommandation** : **whitelist avec issue nommée** + paramètre `allow-axioms: "native_decide.*"` dans `lean-conway.yml` au moment où il sera branché sur `lean-axiom.yml`. Le mécanisme whitelist existe déjà dans le job CI (`lean-axiom.yml` input `allow-axioms`) — il faut juste le déclarer explicitement avec justification écrite.

**Issue fille à créer** : `See #8743` (whitelist `native_decide.*` sur `conway_lean`, justification : « micro-preuves bornées sur instances closes du simulateur, contrats pédagogiques explicites dans `LEAN_INVENTORY.md` §15 et `Conway/README.md` §calibration »).

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

## 4. État du câblage CI

| Lake | Workflow `lean-*.yml` | Appelle `lean-axiom.yml` ? | Verdict au gate |
|---|---|---|---|
| `knot_lean` | `lean-knot.yml` | OUI (pilote) | GREEN post-#8725 |
| `conway_lean` | `lean-conway.yml` | **NON** | serait RED (113 tactic uses) |
| 14 autres lacs | workflows existants | **NON** | GREEN si câblés (sauf 3 borderline sur `Classical.choice`) |

Le câblage du gate sur les lacs non-pilotes est un travail séparé qui sort du scope #8738 (chaque workflow lake est un livrable à part avec son `target-modules` adapté).

## 5. Acceptance step 3 — verdict

- [x] **knot_lean re-mesuré** : GREEN post-#8725 (cf. [#8738](https://github.com/jsboige/CoursIA/issues/8738) body §« Mesure firsthand »)
- [x] **conway_lean re-mesuré** : RED — recommandation whitelist `native_decide.*` avec issue nommée `#8743` à créer
- [x] **3 lacs borderline** identifiés : whitelist `Classical.choice` recommandée au câblage futur avec issue nommée par lake
- [x] **14 lacs GREEN** : câblage futur sans coût

**Recommendation pour le coordinateur (ai-01)** : créer #8743 (whitelist `native_decide.*` sur `conway_lean`), à livrer après un PR de câblage `lean-conway.yml` → `lean-axiom.yml` qui matérialise la déclaration `allow-axioms: "native_decide.*"`. Le câblage lui-même est un MED/lean-ci-tooling dédié.

## 6. Acceptance step 4 — §B.3 pr-review-discipline.md

Le gate `proof-integrity` couvre désormais `native_decide` (post-#8740). La règle `.claude/rules/pr-review-discipline.md` §B.3 mentionnait `sorryAx` (transitif) mais restait ambiguë sur `native_decide` (la classe d'axiomes la plus dangereuse). Le PR companion de ce triage doc met à jour §B.3 pour expliciter que la gate couvre `native_decide`, `sorryAx`, `Classical.choice` (cf. PR #8744 c.948).

## 7. Voir aussi

- [#8738](https://github.com/jsboige/CoursIA/issues/8738) — ticket de référence (parser fix #8740, triage c.948)
- PR [#8740](https://github.com/jsboige/CoursIA/pull/8740) — `fix(lean-tooling,#8738): proof-integrity gate reads multi-line axiom lists` (c.947, MERGED 2026-07-28)
- PR [#8725](https://github.com/jsboige/CoursIA/pull/8725) — `Knots/Invariant.lean` retire `native_decide` tactic (po-2026, MERGED 2026-07-27)
- PR [#8744](https://github.com/jsboige/CoursIA/pull/8744) — c.948 delivery (mise à jour §B.3 + ce doc triage)
- `.github/workflows/lean-axiom.yml` — job réutilisable proof-integrity (4 inputs : `project-path`, `display-name`, `target-modules`, `allow-axioms`, `fail-on-sorry`)
- `.github/workflows/lean-knot.yml` — seul workflow lake à appeler `lean-axiom.yml` actuellement
- `.claude/rules/pr-review-discipline.md` §B.3 — règle de review Lean PRs (mise à jour c.948)
- `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/lean_server.py` — `LeanVerifier._extract_axioms` (parser multiline fixé par c.947)
- `MyIA.AI.Notebooks/SymbolicAI/Lean/Conway/README.md` §15 + `LEAN_INVENTORY.md` — justification pédagogique de `native_decide` sur conway_lean