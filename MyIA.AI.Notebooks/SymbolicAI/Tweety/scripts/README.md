# Scripts Tweety

Ce répertoire contient les scripts utilitaires pour la série Tweety (`Tweety-1-Setup` à `Tweety-9b-*` + `Tweety-Defeasible-Reasoning`). Ils couvrent le téléchargement des dépendances (JARs TweetyProject, Clingo, JDK Zulu portable), la calibration des solveurs SAT, et la vérification de l'intégrité des notebooks.

## Scripts disponibles

### Téléchargement des dépendances

- [download_tweety_tools.py](download_tweety_tools.py) — Télécharge les JARs TweetyProject depuis Maven Central, les ressources (`*.txt`, `*.aba`, `*.aspic`), Clingo (Windows/Linux), SPASS (Linux), JDK Zulu 17 portable, et les bibliothèques natives SAT (Minisat, Lingeling, Picosat). Mode sélectif via flags `--jars`/`--resources`/`--clingo`/`--jdk`/`--native-sat` ou `--all`.

  ```bash
  python scripts/download_tweety_tools.py --all
  ```

### Calibration et comparaison SAT

- [sat_calibration.py](sat_calibration.py) — Recherche des configurations de problèmes SAT où chaque solveur (Minisat, Glucose, Lingeling, Picosat, ...) gagne au moins un test. Utilise `pysat`, timeouts par test, et un budget configurable. Sert de base pour calibrer les exemples pédagogiques.

  ```bash
  python scripts/sat_calibration.py
  ```

- [sat_comparison_demo.py](sat_comparison_demo.py) — Démonstration pédagogique de comparaison de performance des solveurs SAT sur des problèmes classiques de difficulté croissante. Sortie textuelle utilisable directement dans une cellule notebook.

  ```bash
  python scripts/sat_comparison_demo.py
  ```

### Validation et vérification

- [validate_syntax.py](validate_syntax.py) — Parcourt les cellules de code Python des notebooks Tweety et signale les erreurs de syntaxe (`ast.parse`) avec numéro de ligne et identifiant de cellule. Utile en pre-commit ou après une édition manuelle.

  ```bash
  python scripts/validate_syntax.py
  ```

- [verify_all_tweety.py](verify_all_tweety.py) — Vérification complète de la série : structure JSON, configuration kernel (`python3`), présence de cellules markdown/code, prérequis (JDK, JPype, JARs Tweety), et exécution optionnelle via Papermill ou cell-by-cell. Sortie structurée (JSON ou texte) selon les flags.

  ```bash
  # Vérification structurelle seule
  python scripts/verify_all_tweety.py --structure-only

  # Vérification + exécution Papermill (long)
  python scripts/verify_all_tweety.py --execute
  ```

## Dépendances

- Python 3.10+
- `pysat` (calibration/comparaison SAT)
- `JPype1` (notebooks Tweety exécutés)
- JDK 17+ (Zulu portable installable via `download_tweety_tools.py --jdk`)
- Clingo (optionnel, pour notebooks ASP) — installable via `download_tweety_tools.py --clingo`

## Voir aussi

- [Tweety/README.md](../README.md) — Vue d'ensemble de la série Tweety
- [SymbolicAI/scripts/README.md](../../scripts/README.md) — Scripts SymbolicAI niveau série (extraction notebook, installation Clingo)
- [scripts/notebook_tools/](../../../../scripts/notebook_tools/) — Outils génériques (validate / execute / skeleton / analyze)
