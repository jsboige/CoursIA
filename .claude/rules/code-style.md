# Code Style Rules

## General

- No emojis in code, variable names, or generated files
- Follow PEP 8 for Python, standard conventions for C#
- Keep naming professional and descriptive
- Avoid prefixes like "Pure", "Enhanced", "Advanced", "Ultimate" - use descriptive names

## Python

- Python 3.10+ features are OK
- Use type hints for function signatures
- Virtual environment: `venv` with `requirements.txt`

## C# / .NET

- Target framework: .NET 9.0
- .NET Interactive for Jupyter notebooks
- Microsoft.SemanticKernel for AI integrations

## Jupyter Notebooks

- Primary documentation language: French
- Code comments: French or English
- No unnecessary empty cells
- **Notebooks committés AVEC leurs sorties** (règle user 2026-04-26) : les outputs font partie du livrable pédagogique. JAMAIS commit avec `execution_count: null` ou `outputs: []` vidés sans re-exécution. Voir `notebook-conventions.md` section dédiée.
- Clear cell outputs avant commit UNIQUEMENT si les outputs contiennent des données sensibles, sinon laisser les outputs.

## Anti-régression (code de production)

S'applique au **code de production** (preuves Lean/Coq/Agda, fonctions métier appelées, tests, librairies), **PAS** aux cellules d'exercice de notebooks. Règle HARD + protocole 4 étapes + red-flags : [anti-regression.md](anti-regression.md). En bref : ne jamais remplacer une preuve/implémentation existante par `sorry`/stub vide sous prétexte de "fix compilation" ; `grep -c sorry` avant/après ; deletions > insertions sur code métier = red flag.

## Notebooks : stubs d'exercice sans erreur volontaire (C.1)

`raise NotImplementedError` / `assert False` / `1/0` interdits partout (le notebook doit s'exécuter end-to-end) ; patterns corrects (`pass` / `print("Exercice a completer")` / `return None`) + commit AVEC outputs (C.2) : [notebook-conventions.md](notebook-conventions.md). Remplacer un `raise NotImplementedError` legacy par `pass`/`print`/`return None` est **conforme** (anti-régression ne s'applique pas) et doit être mergé sans contestation.
