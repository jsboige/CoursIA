# Scripts Tweety

Ce repertoire contient les scripts utilitaires pour la serie Tweety (`Tweety-1-Setup` a `Tweety-9b-*` + `Tweety-Defeasible-Reasoning`). Ils couvrent le telechargement des dependances (JARs TweetyProject, Clingo, JDK Zulu portable), la calibration des solveurs SAT, et la verification de l'integrite des notebooks.

## Scripts disponibles

### Telechargement des dependances

- [download_tweety_tools.py](download_tweety_tools.py) — Telecharge les JARs TweetyProject depuis Maven Central, les ressources (`*.txt`, `*.aba`, `*.aspic`), Clingo (Windows/Linux), SPASS (Linux), JDK Zulu 17 portable, et les bibliotheques natives SAT (Minisat, Lingeling, Picosat). Mode selectif via flags `--jars`/`--resources`/`--clingo`/`--jdk`/`--native-sat` ou `--all`.

  ```bash
  python scripts/download_tweety_tools.py --all
  ```

### Calibration et comparaison SAT

- [sat_calibration.py](sat_calibration.py) — Recherche des configurations de problemes SAT ou chaque solveur (Minisat, Glucose, Lingeling, Picosat, ...) gagne au moins un test. Utilise `pysat`, timeouts par test, et un budget configurable. Sert de base pour calibrer les exemples pedagogiques.

  ```bash
  python scripts/sat_calibration.py
  ```

- [sat_comparison_demo.py](sat_comparison_demo.py) — Demonstration pedagogique de comparaison de performance des solveurs SAT sur des problemes classiques de difficulte croissante. Sortie textuelle utilisable directement dans une cellule notebook.

  ```bash
  python scripts/sat_comparison_demo.py
  ```

### Validation et verification

- [validate_syntax.py](validate_syntax.py) — Parcourt les cellules de code Python des notebooks Tweety et signale les erreurs de syntaxe (`ast.parse`) avec numero de ligne et identifiant de cellule. Utile en pre-commit ou apres une edition manuelle.

  ```bash
  python scripts/validate_syntax.py
  ```

- [verify_all_tweety.py](verify_all_tweety.py) — Verification complete de la serie : structure JSON, configuration kernel (`python3`), presence de cellules markdown/code, prerequis (JDK, JPype, JARs Tweety), et execution optionnelle via Papermill ou cell-by-cell. Sortie structuree (JSON ou texte) selon les flags.

  ```bash
  # Verification structurelle seule
  python scripts/verify_all_tweety.py --structure-only

  # Verification + execution Papermill (long)
  python scripts/verify_all_tweety.py --execute
  ```

## Dependances

- Python 3.10+
- `pysat` (calibration/comparaison SAT)
- `JPype1` (notebooks Tweety executes)
- JDK 17+ (Zulu portable installable via `download_tweety_tools.py --jdk`)
- Clingo (optionnel, pour notebooks ASP) — installable via `download_tweety_tools.py --clingo`

## Voir aussi

- [Tweety/README.md](../README.md) — Vue d'ensemble de la serie Tweety
- [SymbolicAI/scripts/README.md](../../scripts/README.md) — Scripts SymbolicAI niveau serie (extraction notebook, installation Clingo)
- [scripts/notebook_tools/](../../../../scripts/notebook_tools/) — Outils generiques (validate / execute / skeleton / analyze)
