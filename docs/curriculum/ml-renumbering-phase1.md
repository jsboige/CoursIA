# #5081 — ML (ML.NET) : analyse de renumérotation (phase 1, docs-only)

> **EPIC #5081** — Renumérotation narrative des séries. **Fille sous-série ML.NET (ML-1..ML-9).**
> **Phase 1 = analyse docs-only, ZÉRO rename** (leçon #4737→#4743 : un rename casse les liens inbound).
> Ce document clot la question renumérotation pour la sous-série ML.NET, comme `infer.md`, `search.md`,
> `planners.md`, `pymc.md`, `texte.md`, `video.md` (archivés) et le verdict Sudoku (PR [#9898](https://github.com/jsboige/CoursIA/pull/9898)) l'ont fait
> pour leurs séries.

## Périmètre

La famille `ML/` contient **deux sous-séries au numérotage indépendant** :

1. **`ML/ML.Net/`** (20 notebooks) — le parcours ML.NET canonique `ML-1`..`ML-9` (C# + jumeaux Python
   `*-Python.ipynb`), la variante `ML-4b-ModelComparison`, et le TP capstone. **Cette sous-série est
   l'objet de la présente analyse** : numérotation séquentielle plate, soumise au test #5081.
2. **`ML/DataScienceWithAgents/`** (28 notebooks) — un cours structuré en Days/Labs
   (`1.2-…`, `2.1-…`, `Day1-…/Lab1-…`). Ce track utilise un **schéma de numérotation hiérarchique
   différent** (module.leçon / Day/Lab), pas une séquence plate ML-N. Il **n'entre pas dans le
   périmètre #5081** : la question « l'ordre numérique est-il un tri topologique valide ? » ne se pose
   pas pour un arbre de modules — l'ordre y est porté par la hiérarchie des dossiers (Track/Day), pas
   par un numéro de fichier séquentiel. Cf `texte.md` pour la même exemption (série « plate » vs
   hiérarchique).

## Méthode

Évaluation **firsthand** (lecture directe des notebooks ML-1..ML-9 + du README `ML/`), sur
`origin/main` (`ae9720c1f5`). Le verdict repose sur deux vérifications, conformes à la méthode
phase-1 établie par [#6879](https://github.com/jsboige/CoursIA/pull/6879) :

1. **Tri topologique** — pour chaque notebook, vérifier que tous les prereqs déclarés (champ
   « Prérequis » de la première cellule) pointent vers un notebook **strictement antérieur**.
2. **Carte de l'arc** — comparer l'ordre numérique à l'arc pédagogique documenté dans le README
   (section « Track A : ML.NET » et « Progression recommandée »).

## Verdict : **AUCUNE renumérotation nécessaire pour ML.NET (ML-1..ML-9)**

### Preuve 1 — l'ordre numérique 1→9 est un tri topologique VALIDE du DAG des prereqs

Check automatique sur les 9 numéros canoniques (C# + jumeaux Python) : **0 arête broken-order**.
Plus précisément, le DAG des prereqs déclarés est **vide d'arêtes cross-N** : aucun notebook ML-k ne
déclare un autre ML-j comme prereq. Les prereqs déclarés sont tous **externes** (outils) :

| Notebook | Prereq déclaré (extrait) |
|----------|--------------------------|
| ML-3 (Entraînement & AutoML) Python | `scikit-learn`, `numpy`, `matplotlib` |
| ML-8 (Clustering) Python | `scikit-learn`, `numpy`, `matplotlib` |
| autres | notions de base C# / Python (pas de cross-N) |

Un DAG sans arête cross-N est trivialement un tri topologique valide : il n'y a **aucune** arête à
violenter. L'anti-pattern #5081 (« numérotation d'opportunité » : un notebook inséré à un numéro
disponible sans égard à la pédagogie, cassant l'ordre des prereqs) **ne peut pas se produire** quand
aucun notebook n'en prereq un autre.

### Preuve 2 — l'arc pédagogique documenté suit EXACTEMENT la numérotation

Contrairement à Sudoku (série « plate » de paradigmes indépendants), ML.NET est un **pipeline
séquentiel** : chaque étape prépare la suivante, et le README documente cet arc de façon explicite.
L'ordre numérique 1→9 reflète fidèlement la progression pédagogique :

| Étape | Numéros | Rôle dans le pipeline | Cohérence avec l'ordre |
|------|---------|----------------------|------------------------|
| **Introduction & données** | 1, 2 | Pipeline ML.NET (`IDataView`), encodage, features | Fondations avant tout — correct en tête |
| **Entraînement** | 3 | SDCA, LightGBM, **AutoML** (leaderboard discriminateur) | Après la prép. données (2) — correct |
| **Évaluation** | 4 (+4b) | Cross-validation, Permutation Feature Importance | **« Crucial »** selon README ; après l'entraînement qu'elle juge — correct |
| **Applications** | 5, 6, 7 | Séries temporelles → export **ONNX** (prod) → **Recommandation** | Pipeline maîtrisé → cas d'usage — correct |
| **Non-supervisé** | 8, 9 | Clustering K-Means (RFM) → Anomaly Detection (Randomized PCA) | Changement de paradigme en fin — correct |
| **Capstone** | TP | Prévision de ventes (ML.NET + Infer.NET, régression bayésienne) | Intégration finale — correct |

Le README « Progression recommandée » confirme : les parcours « Data Scientist » et « Enterprise .NET »
empruntent ML-1→ML-2→ML-3→ML-4 dans l'ordre numérique. L'arc est **volontairement séquentiel** et la
numérotation le respecte intégralement.

### Structure jumeaux — pas un défaut de numérotation

Les jumeaux Python (`ML-1-Introduction-Python.ipynb`, …, `ML-9-Anomaly-Detection-Python.ipynb`) sont
co-localisés et portent le **même numéro** que leur pendant C# (parité #4956, CLOSED). Ce n'est pas
de la « numérotation d'opportunité » : c'est la convention de parité .NET⇄Python, où chaque jumeau
hérite du numéro du concept qu'il illustre. La variante `ML-4b-ModelComparison` étend ML-4 (évaluation)
sans en rompre l'ordre. Aucun renumérotage impliqué.

## Point de vigilance (hors-scope de #5081)

La sous-série est **séquentiellement riche mais prereq-déclarativement vide** : le pipeline 1→9 est
réel (chaque étage prépare le suivant), mais aucun notebook ne le **déclare formellement** comme
prereq. C'est l'inverse de Sudoku (plate en arc, plate en prereqs) et d'Infer (riche en arc, riche en
prereqs déclarés). Si l'on voulait rendre la dépendance explicite (ex. ML-4 déclare ML-3, ML-7 déclare
ML-6), ce serait un travail d'**enrichissement des en-têtes** — distinct de la renumérotation, et hors
périmètre phase-1. Statu quo recommandé : le README porte déjà l'arc.

## Voir aussi

- EPIC [#5081](https://github.com/jsboige/CoursIA/issues/5081) — renumérotation narrative.
- Verdicts sœurs : [Sudoku](sudoku-renumbering-phase1.md) (même auteur, série plate),
  [Infer](../archive/curriculum-renumbering-phase1/infer.md),
  [Search](../archive/curriculum-renumbering-phase1/search.md),
  [Planners](../archive/curriculum-renumbering-phase1/planners.md),
  [PyMC](../archive/curriculum-renumbering-phase1/pymc.md),
  [Texte](../archive/curriculum-renumbering-phase1/texte.md),
  [Video](../archive/curriculum-renumbering-phase1/video.md).
- [#4956](https://github.com/jsboige/CoursIA/issues/4956) (CLOSED) — parité .NET⇄Python (jumeaux).
