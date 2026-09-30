# Scripts Sudoku archivés — exploration EPF (avril 2026)

Ce dossier conserve les six scripts de l'exploration « EPF » du solveur de
Sudoku, archivés le 2026-04-28. L'effort a été modularisé dans
[`../core/`](../core/) (dataset, models, training, evaluate, solvers,
generation, graph) et repris par [`../train_v4.py`](../train_v4.py).

Les scripts archivés gardent dans leur en-tête leur **chemin d'origine**
(`scripts/sudoku_epf_gpu_train.py`, etc.) : un script ressuscité doit rester
utilisable sans réécriture de ses chemins relatifs (critère 4 de la
[convention](../../../docs/reference/_archive-convention.md)).

## Registre de disposition

| Script | Verdict | Superseded by | Verdict recorded in |
|---|---|---|---|
| `epf_experiment.py` | OBSOLETE (2026-04-28) — expérience d'architecture EPF (Conv+BN x3 + Dense) comparée au ResCNN courant, phases 50K puis 200K | [`../core/`](../core/) + [`../train_v4.py`](../train_v4.py) | En-tête du fichier (`Original: scripts/sudoku_epf_experiment.py`) ; ce registre |
| `epf_v1.py` | OBSOLETE (2026-04-28) — entraînement GPU d'une pile Conv2D EPF (~7,6 M params), cible 96,8 % de grille | [`../core/`](../core/) + [`../train_v4.py`](../train_v4.py) | En-tête du fichier (`Original: scripts/sudoku_epf_gpu_train.py`) ; ce registre |
| `epf_v2.py` | OBSOLETE (2026-04-28) — variante v1 à **perte masquée** (les cellules déjà remplies ne comptent plus dans la perte) | [`../core/`](../core/) + [`../train_v4.py`](../train_v4.py) | En-tête du fichier (`Original: scripts/sudoku_epf_gpu_train_v2.py`) ; ce registre |
| `epf_v3.py` | OBSOLETE (2026-04-28) — variante ResNet profonde (8 blocs résiduels, canaux élargis), perte masquée, OneCycleLR | [`../core/`](../core/) + [`../train_v4.py`](../train_v4.py) | En-tête du fichier (`Original: scripts/sudoku_epf_gpu_train_v3.py`) ; ce registre |
| `iterative_eval.py` | OBSOLETE (2026-04-28) — évaluation du solveur itératif (prédiction puis re-injection des cellules) | [`../core/`](../core/) + [`../train_v4.py`](../train_v4.py) | En-tête du fichier (`Original: scripts/sudoku_iterative_eval.py`) ; ce registre |
| `test_student.py` | OBSOLETE (2026-04-28) — test du modèle étudiant EPF `sudoku_solver_final.h5` | [`../core/`](../core/) + [`../train_v4.py`](../train_v4.py) | En-tête du fichier (`Original: scripts/test_student_model.py`) ; ce registre |

## Vérifications faites à la mise au standard (2026-09-25)

- **Critère 2/3 (zéro référence, zéro import)** — `git grep` des noms d'origine
  (`sudoku_epf_experiment`, `sudoku_epf_gpu_train`, `sudoku_iterative_eval`,
  `test_student_model`) sur `*.py` / `*.ipynb` / `*.md` : **aucun consommateur**
  hors de ce dossier.
- **Critère 4 (successeur existe)** — [`../core/`](../core/) et
  [`../train_v4.py`](../train_v4.py) sont présents sur `main`.
- Les six fichiers portaient **déjà** leur en-tête de disposition (archivage
  2026-04-28) : cette passe ajoute le registre qui manquait, elle ne réécrit
  aucun en-tête.