# Archive — Notebooks racine Search (legacy)

Ce répertoire contient les anciennes versions des notebooks Python qui se trouvaient à la racine `MyIA.AI.Notebooks/Search/` avant la réorganisation par le plan C201 (#5081).

## Fichiers archivés

### `CSPs_Intro.ipynb`

- **Date d'archivage** : 2026-07-03
- **Raison** : Remplacé par la sous-série `Part2-CSP/` (9 notebooks dédiés : `CSP-1-Fundamentals.ipynb` à `CSP-9-Advanced-Topics.ipynb`) qui introduit les concepts progressivement (contraintes, propagation, backtracking, AC-3, recherche locale) plutôt qu'en un seul document monolithique.
- **Contenu original** : introduction aux CSPs (Constraint Satisfaction Problems) — définitions, formalisme, exemples jouets.
- **Nouvelle structure** : `Part2-CSP/CSP-1-Fundamentals.ipynb` couvre les mêmes bases avec un cadre unifié (variables/domaines/contraintes), puis les notebooks 2 à 9 développent chaque technique.

### `Exploration_non_informée_et_informée_intro.ipynb`

- **Date d'archivage** : 2026-07-03
- **Raison** : Remplacé par la sous-série `Part1-Foundations/` qui sépare clairement exploration non-informée (`Search-2-Uninformed.ipynb` : BFS, DFS, UCS, IDS, profondeur itérative) et exploration informée (`Search-3-Informed.ipynb` : greedy best-first, A*, variantes pondérées) en deux notebooks distincts plutôt qu'un document mêlant les deux familles.
- **Contenu original** : survol des algorithmes d'exploration non-informée (BFS/DFS) et informée (A*) en un seul notebook.
- **Nouvelle structure** :
  - `Part1-Foundations/Search-1-Landscape.ipynb` — panorama
  - `Part1-Foundations/Search-2-Uninformed.ipynb` — exploration non-informée
  - `Part1-Foundations/Search-3-Informed.ipynb` — exploration informée et heuristiques

## Vérification de la migration

- **Part1-Foundations/** : 11 notebooks (Search-1 à Search-11), couverture exhaustive incluant uninformed + informed + variantes (IDA*, SMA*, RBFS) + benchmarks.
- **Part2-CSP/** : 9 notebooks (CSP-1 à CSP-9), couverture CSPs du fondamental aux techniques avancées (AC-3, forward checking, MAC, recherche locale).
- **Recherche linéaire dans la racine** : `find MyIA.AI.Notebooks/Search/ -maxdepth 1 -name "*.ipynb" -not -path "*/archive/*"` ne renvoie plus que les sous-répertoires `Part1-Foundations/`, `Part2-CSP/`, `Part3-Advanced/`, `Part4-Metaheuristics/`, `search_lean/`, `archive/` (C204-PR #5187) et (C205-PR #5193) ont déjà migré les autres familles.

## Référence historique

- **Audit déclencheur** : #5081 (audit narratif des séries du dépôt, slice Search)
- **PR d'archivage** : C209 tranche 8/8 du plan C201
- **Précédents archivages dans le dépôt** : `SymbolicAI/archive/` (Tweety monolithique remplacé par 7 notebooks thématiques, 2026-01-23)
- **Documentation connexe** : le label "legacy à archiver" était explicite dans `Search/README.md` lignes 327 + 500-501 avant cette PR

## Note de préservation

Les notebooks archivés sont conservés **tels quels** (contenu, outputs) — preuve de préservation conformément à la règle *Consolider ≠ Archiver* (CLAUDE.md global). Aucune modification du contenu pédagogique, aucune suppression de cellule. Seuls les chemins d'accès ont changé : racine → `archive/`.

Si un lien historique pointe encore vers la racine (par exemple depuis un ancien commentaire), utiliser ce `README.md` comme point de redirection vers les nouvelles sous-séries.