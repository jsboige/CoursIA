# Anti-régression : préserver le travail existant

S'applique au **code de production** (preuves Lean/Coq/Agda, fonctions métier appelées, tests, librairies). **Pas** aux cellules d'exercice étudiant — celles-ci doivent justement être stubbées sans `raise NotImplementedError` (cf [notebook-conventions.md](notebook-conventions.md) règle C.1).

**Contexte complet, patterns détaillés, incidents et workflow audit** : [docs/anti-regression-detail.md](../../docs/anti-regression-detail.md).

## Règle HARD

**INTERDIT** : remplacer une preuve formelle ou une implémentation existante par `sorry` / stub vide / `return None` / `pass`, sans diagnostic explicite et tactiques d'adaptation tentées.

Commits "fix compilation" / "Mathlib fix" / "lint fix" / "simplify" avec **deletions > insertions** sur code métier sont **red flag** par défaut.

## Patterns red-flag (résumé)

### Lean / Coq / Agda
- `theorem foo := by <tactics>` → `theorem foo := by sorry` = **Régression**
- `def foo := <implémentation>` → `def foo := sorry` = **Régression**
- Augmentation de `grep -c sorry file.lean` non justifiée = PR à contester

### Code Python/applicatif (production)
- `def foo(...):` avec corps calculé → `def foo(...): pass` = Régression sauf si fonction n'est plus appelée
- Test avec assertions → `@pytest.skip` sans issue référencée = Régression
- `return <calcul>` (fonction utilisée) → `return None` = Régression

### Notebooks pédagogiques — IMPORTANT
- `raise NotImplementedError(...)` → `pass` / `print` / `return None` = **PAS une régression, conforme règle user 2026-04-26**
- Cellule `# Solution` (exemple résolu) → stub = **Régression de contenu** (suppression INTERDITE)
- 5 exercices numérotés → 2 exercices = Régression de contenu

Tableaux complets dans [docs/anti-regression-detail.md](../../docs/anti-regression-detail.md#patterns-red-flag-détaillés-tables-complètes).

## Protocole avant suppression (HARD)

Si tu veux supprimer du code/preuve dans un commit, **répondre écrit** à ces questions dans le commit :

1. Citer l'erreur compilateur exacte ou test échoué nommé (pas "ça compilait pas")
2. Tenter 3 adaptations tactiques avant la suppression (instance ajoutée, tactique alternative, hypothèse ajoutée)
3. PR dédiée labellisée `debt`/`regression-accepted` avec sign-off user pour toute régression assumée
4. `git diff --stat` cohérent avec l'intention

Si une seule question n'a pas de réponse écrite dans le commit : ne pas commiter, demander au user/coordinateur.

## Détection (audit avant merge)

Pour une PR avec deletions > insertions sur code métier :

```bash
# Sorry introduits dans Lean
git diff <base>..<pr-branch> -- '*.lean' | grep -E "^\+.*sorry"

# Solution → stub dans notebooks
git diff <base>..<pr-branch> -- '*.ipynb' | grep -E "^[-+].*Solution|^[-+].*pass"

# Compter sorry avant/après
grep -c sorry file.lean
```

Workflow audit complet (rogue commits historiques) et requêtes git utiles : [docs/anti-regression-detail.md](../../docs/anti-regression-detail.md#détection-après-coup-audit-rogue-commits).

## Incident référence

2026-04-24 : commit "Mathlib compilation fixes" (#488 H-2) a remplacé 9 preuves Arrow.lean par `sorry`, perte d'une semaine de port Lean ; restauration via #527. Détails dans [docs/anti-regression-detail.md](../../docs/anti-regression-detail.md#incident-fondateur-2026-04-24-arrowlean).
