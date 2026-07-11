# Inventaire i18n des projets Lean 4 — couverture FR/EN

Inventaire transverse de la **couverture i18n** (FR canonique + EN sibling) des
fichiers `.lean` de nos lakes, à la date 2026-07-11. Source de vérité : conventions
ratifiées par ai-01 (2026-07-04, issue
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

## Résumé par lake

| Lake | FR canonique | EN sibling | Couverture fichiers | Couverture lignes FR | Statut |
|------|-------------:|-----------:|--------------------:|---------------------:|--------|
| `learning_theory_lean` | 19 | 18 | 18/19 = **95 %** | ~554 | EXCELLENT |
| `sudoku_lean` | 5 | 4 | 4/5 = **80 %** | ~62 | BON |
| `repeated_games_lean` | 6 | 4 | 4/6 = **67 %** | ~65 | PARTIEL (c.356 = 4 tranches sur 6) |
| `minimax_lean` | 5 | 4 | 4/5 = **80 %** | ~41 | BON |
| `cooperative_games_lean` | 5 | 3 | 3/5 = **60 %** | ~819 | PARTIEL |
| `game_theory_lean` | 12 | 8 | 8/12 = **67 %** | ~1702 | PARTIEL (multi-lib) |
| `social_choice_lean` | 10 | 7 | 7/10 = **70 %** | ~790 | PARTIEL |
| `sensitivity_lean` | 6 | 4 | 4/6 = **67 %** | ~8 + ~6 inline | PARTIEL |
| `calibration_lean` | 5 | 3 | 3/5 = **60 %** | ~95 + ~15 inline | PARTIEL |
| `finiteness_lean` | 3 | 1 | 1/3 = **33 %** | ~17 | PARTIEL |
| `conway_cgt_lean` | 2 | 0 | 0/2 = **0 %** | ~0 (4 markers header only) | **À FAIRE** |
| `knot_lean` | 8 | 0 | 0/8 = **0 %** | ~584 | **À FAIRE** |
| `grothendieck_lean` | 26 | 0 | 0/26 = **0 %** | ~222 | **À FAIRE** |
| `conway_lean` | 27 | 0 | 0/27 = **0 %** | ~1894 | **À FAIRE** (gros) |
| `mathlib_examples` | 3 | 0 | 0/3 = **0 %** | ~0 | **À FAIRE** (peut-être trivial) |
| `social_choice_lean_peters` | 2 | 0 | 0/2 = **0 %** | ~0 | **HORS SCOPE** (vendored, `_peters`) |

---

## Détail par lake

### 1. `learning_theory_lean` — EXCELLENT (95 %)

**Chemin** : `MyIA.AI.Notebooks/ML/learning_theory_lean/`

19 fichiers FR canoniques, **18 fichiers EN siblings** (`*_en.lean`). Seul le
`lakefile.lean` n'a pas de sibling (les lakefiles sont par convention
aglistiques — pas de docstrings utilisateur).

**Mantra** : "learning_theory_lean = Perceptron (Novikoff) + PacLearning
(Valiant), 0 sorry, canon i18n à 95 %". Le seul module qui pourrait servir de
**référentiel de convention** (option A = fichiers siblings) — c'est ici que
la convention FR+EN siblings a été validée en premier.

**Suivi** : aucun ajout nécessaire ; surveiller la dérive (Drift-CI byte-identity).

### 2. `sudoku_lean` — BON (80 %)

**Chemin** : `MyIA.AI.Notebooks/Sudoku/sudoku_lean/`

5 fichiers FR canoniques, 4 fichiers EN siblings (`Sudoku.lean`, `Basic.lean`,
`Propagation.lean`, `ExactCover.lean`). Le `lakefile.lean` est aglistique.
C.361 README de-spaghetti Phase 3 livré (#6080, ce cycle).

**Mantra** : "sudoku_lean = soundness propagation + exact-cover, 0 sorry, lake
pédagogique bilingue canon". C'est le candidat PR pilote traditionnel — déjà
bilingue, le delta est seulement cosmétique (c.361 README).

### 3. `repeated_games_lean` — PARTIEL (67 %)

**Chemin** : `MyIA.AI.Notebooks/GameTheory/repeated_games_lean/`

6 fichiers FR canoniques, 4 fichiers EN siblings (`Stage`, `Discounting`,
`GrimTrigger`, `Folk`). C.356 PR #6048 a livré **4 tranches sur 6** (Stage,
Discounting, GrimTrigger, Folk). Restant : `RepeatedGames.lean` (agrégateur) +
`lakefile.lean` (aglistique).

**Mantra** : "RepeatedGames = stage game + Folk theorem, 0 sorry sur le
théorème-phare grim trigger, bilingue FR+EN sur 4/6 modules". Suite à
trancher en c.363+ (les 2 restants sont triviaux).

### 4. `game_theory_lean` — PARTIEL (67 %)

**Chemin** : `MyIA.AI.Notebooks/GameTheory/game_theory_lean/`

**Multi-lib lean** (cf. c.299 StableMarriage + c.306 CooperativeGames +
c.357 SocialChoice regroupement) : 12 fichiers FR canoniques, 8 fichiers EN
siblings. La convention `_en` namespace est appliquée par lean_lib (`StableMarriage`,
`CooperativeGames`, `SocialChoice` — chacun avec son sibling `_en`).

**Mantra** : "game_theory_lean = cohorte multi-lib 3 lean_lib distincts
(StableMarriage + CooperativeGames + SocialChoice), 0 sorry sur le
théorème-phare, bilingue sur 8/12 modules". Lake = pivot central du EPIC
#4365 regroupement.

### 5. `social_choice_lean` — PARTIEL (70 %)

**Chemin** : `MyIA.AI.Notebooks/GameTheory/social_choice_lean/`

10 fichiers FR canoniques, 7 fichiers EN siblings. Reste : 3 modules internes
(utilitaires, lemmas privés).

### 6. `minimax_lean` — BON (80 %)

5 fichiers FR canoniques, 4 fichiers EN siblings. Coverage élevée.

### 7. `cooperative_games_lean` — PARTIEL (60 %)

5 fichiers FR canoniques, 3 fichiers EN siblings. ~819 lignes FR — lake
substantiel à compléter.

### 8. `sensitivity_lean` — PARTIEL (67 %)

6 fichiers FR canoniques, 4 fichiers EN siblings + **6 markers inline
bilingues** dans le FR canonique (pattern hybride). Le ratio de couverture est
similaire à `repeated_games_lean` mais le contenu EN est intégré au FR
canonique plutôt qu'en fichier sibling. **Cas d'étude intéressant pour
arbitrer entre Option A (sibling) vs Option B (inline)**.

### 9. `calibration_lean` — PARTIEL (60 %)

5 fichiers FR canoniques, 3 fichiers EN siblings + **15 markers inline
bilingues**. Lake = composant harnais de calibration (déplacé depuis
GameTheory, #1764). Hybridation similaire à `sensitivity_lean`.

### 10. `finiteness_lean` — PARTIEL (33 %)

3 fichiers FR canoniques, 1 fichier EN sibling. Le ratio est faible parce que
les 2 fichiers non-traduits sont des utilitaires internes. ~17 lignes FR
uniquement.

### 11. `conway_cgt_lean` — À FAIRE (0 %)

**Chemin** : `MyIA.AI.Notebooks/GameTheory/conway_cgt_lean/`

2 fichiers FR canoniques, **0 fichier EN sibling**. Le fichier `CGTTour.lean`
(297 lignes) contient 4 markers `English` dans le header seulement — le
contenu pédagogique des sections 2-4 est FR uniquement. **Candidat PR
pilote** (cycle c.363+) : ajouter les sections EN sur les `## 2`, `## 3`, `## 4`
en suivant le pattern `RepeatedGames` (sibling `CGTTour_en.lean`).

**Mantra** : "conway_cgt_lean = tour pédagogique de la lib CGT de vihdzp
(combinatorial-games, Lake dependency), 0 sorry, bilinguisation trivialement
extensible". Le contenu pédagogique est en français depuis l'origine —
bilinguisation = gain pédagogique EN, sans risque de régression code.

### 12. `knot_lean` — À FAIRE (0 %)

**Chemin** : `MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/`

8 fichiers FR canoniques, **0 fichier EN sibling**. ~584 lignes FR. Lake =
**recherche** (théorie des nœuds, EPIC #2874). Les `sorry` sont des
définitions non-définies (`AreMutants`, `alexanderPolynomial`,
`IsSmoothlySlice`, `IsTopologicallySlice := sorry`) et des preuves de
transfert classique ouvertes. **Niveau recherche** — bilinguisation = gain
pédagogique mais sans urgence (lake non-PEDA).

### 13. `grothendieck_lean` — À FAIRE (0 %)

**Chemin** : `MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/`

26 fichiers FR canoniques, **0 fichier EN sibling**. ~222 lignes FR + le
reste est code pur sans docstring. Lake = **recherche** (EPIC #2159
Grothendieck). Gros volume (26 fichiers) mais le contenu est essentiellement
du code de formalisation sans pédagogie textuelle — bilinguisation = faible
gain marginal.

### 14. `conway_lean` — À FAIRE (0 %) (gros volume)

**Chemin** : `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/`

**27 fichiers FR canoniques**, **0 fichier EN sibling**. ~1894 lignes FR
canonique (le plus gros contributeur de lignes FR non-bilingues du repo).
Lake = **cœur PEDA Conway** (Life + Doomsday + FRACTRAN + Look-and-Say + Nim +
Angel + **Hashlife**).

**Mantra** : "conway_lean = série Conway hommage (Life + Doomsday + FRACTRAN +
Look-and-Say + Nim + Angel), ~1894 lignes FR canoniques, 4 sorries
Hashlife (cibles prover), 0 EN siblings". Bilinguisation = gros effort mais
gain pédagogique élevé (le lake le plus visité pédagogiquement après
`learning_theory_lean`).

**Stratégie recommandée** : bilinguisation par **PR incrémentaux** lake par
sous-série (Life en premier, vu l'attention actuelle sur Hashlife).

### 15. `mathlib_examples` — À FAIRE (0 %)

3 fichiers FR canoniques, **0 fichier EN sibling**. Lake = référence
(quelques exemples Mathlib re-formatés). Contenu FR quasi-nul (code sans
docstring utilisateur). **Bilinguisation = faible priorité**.

### 16. `social_choice_lean_peters` — HORS SCOPE

2 fichiers FR canoniques, **0 fichier EN sibling**. **Vendored** (lib Peters
intégrée, dépendance Lake). Convention i18n = **hors scope** pour les libs
vendored (cf. `readme-french-first.md` règle périmètre).

---

## Cibles PR pilote (cycles suivants)

| Priorité | Lake | Effort | Gain pédagogique | Risque |
|---------:|------|--------|------------------|--------|
| **1** | `conway_cgt_lean` | ~150 lignes (1 sibling `CGTTour_en.lean`) | Élevé (CGTTour est lu par tout visiteur GT) | Faible (0 sorry, docstring only) |
| 2 | `repeated_games_lean` (2 restants) | ~50 lignes | Moyen | Faible |
| 3 | `knot_lean` | ~600 lignes (8 siblings) | Moyen (lake recherche) | Moyen (gros diff) |
| 4 | `conway_lean` | ~2000 lignes (27 siblings) | Très élevé | Élevé (gros diff,湖 build à vérifier) |
| 5 | `grothendieck_lean` | ~250 lignes (26 siblings) | Faible | Moyen |

**Recommandation c.363+** : démarrer par **`conway_cgt_lean`** (cible #1)
parce que (a) scope minimal, (b) 0 sorry, (c) contenu 100 % pédagogique
(donc bilinguisation = pur gain sans risque code), (d) visitor-facing.

---

## Inventaire brut — sortie reproductible

Commande de reproduction (à exécuter depuis la racine du dépôt) :

```bash
for lake in MyIA.AI.Notebooks/SymbolicAI/Lean/*/ MyIA.AI.Notebooks/GameTheory/*/ MyIA.AI.Notebooks/ML/*/ MyIA.AI.Notebooks/Sudoku/*/; do
  if [ -f "$lake/lakefile.lean" ]; then
    lake_name=$(basename "$lake")
    fr=$(find "$lake" -name '*.lean' -not -path '*.lake*' -not -name '*_en.lean' 2>/dev/null | wc -l)
    en=$(find "$lake" -name '*_en.lean' -not -path '*.lake*' 2>/dev/null | wc -l)
    echo "$lake_name: fr_files=$fr en_files=$en"
  fi
done
```

Sortie 2026-07-11 (epoch de cet inventaire) :

```
calibration_lean: fr_files=5 en_files=3
conway_lean: fr_files=27 en_files=0
finiteness_lean: fr_files=3 en_files=1
grothendieck_lean: fr_files=26 en_files=0
knot_lean: fr_files=8 en_files=0
mathlib_examples: fr_files=3 en_files=0
sensitivity_lean: fr_files=6 en_files=4
conway_cgt_lean: fr_files=2 en_files=0
cooperative_games_lean: fr_files=5 en_files=3
game_theory_lean: fr_files=12 en_files=8
minimax_lean: fr_files=5 en_files=4
repeated_games_lean: fr_files=6 en_files=4
social_choice_lean: fr_files=10 en_files=7
social_choice_lean_peters: fr_files=2 en_files=0
learning_theory_lean: fr_files=19 en_files=18
sudoku_lean: fr_files=5 en_files=4
```

---

## Voir aussi

- [LEAN_INVENTORY.md](LEAN_INVENTORY.md) — inventaire sorry/modules par lake (même registre)
- [GameTheory/LEAN_INVENTORY.md](../../GameTheory/LEAN_INVENTORY.md) — version GameTheory
- Issue [#4980](https://github.com/jsboige/CoursIA/issues/4980) — parente (open, tranche 1/3)
- Issue [#1650](https://github.com/jsboige/CoursIA/issues/1650) — EPIC traduction multilingue
- [`readme-french-first.md`](../../.claude/rules/readme-french-first.md) — convention sister `README.en.md`
- PR #6048 (c.356 RepeatedGames root bilingue FR+EN) — convention ratifiée
- PR #6040 (c.357 Lean regroupement SocialChoice) — multi-lib lean_lib pattern