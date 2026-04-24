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
- Clear cell outputs before committing if outputs contain sensitive data

## Anti-régression : ne pas supprimer le travail existant

Règle de premier ordre, applicable à tous les fichiers :

- **Ne jamais remplacer une preuve/implémentation fonctionnelle existante par `sorry`/`pass`/`NotImplementedError`/stub vide** sous prétexte de "fix compilation". Diagnostiquer la vraie cause et adapter tactiquement.
- Commits "fix compilation" / "lint fix" / "simplify" / "Mathlib update fix" avec **deletions > insertions** sur code métier = red flag à investiguer avant merge.
- Fichiers de vérification formelle (`*.lean`, `*.v`, `*.agda`) : `sorry` injecté = axiome implicite = perte de confiance. Compter avec `grep -c sorry` avant/après chaque commit.
- Tests : pas de `@pytest.skip` ni `assert True` pour contourner un test cassé — corriger le test ou documenter pourquoi on l'accepte.
- Cellules notebook pédagogique : ne pas effacer une cellule `# Solution` existante sans issue explicite.

**Voir `anti-regression.md` pour le workflow complet de détection + review.**
