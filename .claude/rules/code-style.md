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

## Lean (i18n)

EPIC **#4980** — convention ratifiée par user 2026-07-04 (Option A, deux commentaires user datés 2026-07-04T11:58Z et 14:52Z sur l'issue, addendum mécanisme FR/EN inclus), voir l'inventaire de référence [`docs/lean/i18n-inventory-cycle-38.md`](../../docs/lean/i18n-inventory-cycle-38.md) + pilote livré PR #5883 (2026-07-10, [`CooperativeGames.lean`](../../MyIA.AI.Notebooks/GameTheory/cooperative_games_lean/CooperativeGames.lean) root aggregator bilingue inline FR+EN).

- **Docstrings en français** par défaut dans les `*.lean` own (i.e. hors `.lake/packages/`, `_peters/`, `agent_tests/prover/session_state/reference_docs/`, et libs vendored).
- **Traduction anglaise optionnelle** pour les lakes destinés à une audience externe (publication, papier, dépôt public). Modèle **sibling pair** `Foo.lean` / `Foo_en.lean` :
  - Suffixe `_en` sur le **namespace** (`namespace FooLean` ↔ `namespace FooLean_en`) et sur les **imports** (`import Foo.Bar` ↔ `import Foo.Bar_en`) — anti-collision de noms.
  - Les **énoncés de théorèmes/lemmes**, **tactiques Lean**, **noms de lemmes**, **références Mathlib** restent en anglais (compat Mathlib 4, tactic DSL, lemmas officiels).
  - Seules les **docstrings `/-- ... -/`** et **commentaires `-- ...`** diffèrent entre les deux fichiers. **Préservation byte-identity** sur le reste (signatures, preuves, tactiques) — vérifiable par diff.
- **Pas de bloc bilingue inline** dans un même fichier (Option B rejetée : coût double + drift FR/EN + biais qualité).
- **Hors scope** (status quo) : `.lake/packages/` (Mathlib 4 vendored), `_peters/` (lake externe), `agent_tests/prover/session_state/reference_docs/` (fixtures tiers), libs vendored tierces (`foundry-lib/lib/**`).
- **Rollout** : 6/11 lakes déjà FR-first (cycle 16+) — pas de migration disruptive. Backlog : PR pilote `Sudoku/sudoku_lean` (cycle 39) puis 4 lakes EN-dominants (`cooperative_games_lean`, `social_choice_lean`, `stable_marriage_lean`, `decision_theory_lean`).

## Anti-régression (code de production)

S'applique au **code de production** (preuves Lean/Coq/Agda, fonctions métier appelées, tests, librairies), **PAS** aux cellules d'exercice de notebooks. Règle HARD + protocole 4 étapes + red-flags : [anti-regression.md](anti-regression.md). En bref : ne jamais remplacer une preuve/implémentation existante par `sorry`/stub vide sous prétexte de "fix compilation" ; `grep -c sorry` avant/après ; deletions > insertions sur code métier = red flag.

## Notebooks : stubs d'exercice sans erreur volontaire (C.1)

`raise NotImplementedError` / `assert False` / `1/0` interdits partout (le notebook doit s'exécuter end-to-end) ; patterns corrects (`pass` / `print("Exercice a completer")` / `return None`) + commit AVEC outputs (C.2) : [notebook-conventions.md](notebook-conventions.md). Remplacer un `raise NotImplementedError` legacy par `pass`/`print`/`return None` est **conforme** (anti-régression ne s'applique pas) et doit être mergé sans contestation.
