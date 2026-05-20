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

## Anti-régression : ne pas supprimer le travail existant (code de production)

Règle applicable au **code de production** (preuves Lean, fonctions métier appelées, tests, librairies) — **PAS** aux cellules d'exercice de notebooks pédagogiques (voir section dédiée ci-dessous).

- **Ne jamais remplacer une preuve formelle ou une implémentation fonctionnelle existante par `sorry`/stub vide** sous prétexte de "fix compilation". Diagnostiquer la vraie cause et adapter tactiquement.
- Commits "fix compilation" / "lint fix" / "simplify" / "Mathlib update fix" avec **deletions > insertions** sur code métier = red flag à investiguer avant merge.
- Fichiers de vérification formelle (`*.lean`, `*.v`, `*.agda`) : `sorry` injecté = axiome implicite = perte de confiance. Compter avec `grep -c sorry` avant/après chaque commit.
- Tests : pas de `@pytest.skip` ni `assert True` pour contourner un test cassé — corriger le test ou documenter pourquoi on l'accepte.
- Cellules notebook pédagogique : ne pas effacer une cellule `# Solution` existante (exemple résolu démonstratif) sans issue explicite.

## Notebooks pédagogiques : pas de cellule en erreur (règle user 2026-04-26)

Règle distincte de l'anti-régression : dans un notebook, **aucune cellule ne doit échouer volontairement**. En particulier :

- **`raise NotImplementedError(...)` est INTERDIT partout dans un notebook** (top-level, méthode, fonction utilitaire). Les scripts de validation trackent les cellules en erreur comme bugs à corriger, donc une erreur volontaire pollue les rapports.
- **Pour signaler une cellule à compléter par l'étudiant** : utiliser `pass`, `print("Exercice a completer")`, ou `return None` selon le contexte. Préserver tous les commentaires `# TODO` et `# Indice` au-dessus.
- **Toute autre erreur volontaire interdite aussi** : `assert False`, `1/0`, `raise X("...")`, etc. Le notebook doit s'exécuter de bout en bout sans erreur même quand les exercices ne sont pas complétés.
- **Conséquence pour la review** : remplacer un `raise NotImplementedError` legacy par `pass`/`print`/`return None` dans un notebook est conforme à cette règle et doit être mergé sans contestation.

**Voir `anti-regression.md` pour le workflow complet de détection + review du code de production, et CLAUDE.md section "RÈGLE CRITIQUE - Anti-régression" pour le détail des stubs d'exercice.**
