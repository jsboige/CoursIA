# Anti-régression : préserver le travail existant

S'applique au **code de production** (preuves Lean/Coq/Agda, fonctions métier appelées, tests, librairies). **Pas** aux cellules d'exercice étudiant — celles-ci doivent justement être stubbées sans `raise NotImplementedError` (cf [notebook-conventions.md](notebook-conventions.md) règle C.1).

**Contexte complet, patterns détaillés par langage, requêtes audit, incidents** : [docs/anti-regression-detail.md](../../docs/reference/anti-regression-detail.md).

## Règle HARD

**INTERDIT** : remplacer une preuve formelle ou une implémentation existante par `sorry` / stub vide / `return None` / `pass`, sans diagnostic explicite et tactiques d'adaptation tentées.

Commits "fix compilation" / "Mathlib fix" / "lint fix" / "simplify" avec **deletions > insertions** sur code métier sont **red flag** par défaut.

## Red-flag rapides

- **Lean/Coq/Agda** : `theorem foo := by <tactics>` → `:= by sorry` = régression. `grep -c sorry` qui monte sans justification = PR contestée.
- **Python production** : corps calculé → `pass` (fonction encore appelée) ; `@pytest.skip` sans issue référencée ; `return None` à la place du calcul.
- **Notebooks pédagogiques** : `raise NotImplementedError` → `pass`/`print`/`return None` = **conforme** (règle user 2026-04-26). Mais cellule `# Solution` / `# Exemple résolu` supprimée = **régression de contenu INTERDITE**.

Tables complètes par langage : [docs/anti-regression-detail.md](../../docs/reference/anti-regression-detail.md#patterns-red-flag-détaillés-tables-complètes).

## Protocole avant suppression (HARD)

Si tu veux supprimer du code/preuve, **réponses écrites dans le commit** :

1. Citer l'erreur compilateur exacte ou test échoué nommé (pas "ça compilait pas")
2. Tenter 3 adaptations tactiques avant la suppression
3. PR dédiée `debt`/`regression-accepted` avec sign-off user pour toute régression assumée
4. `git diff --stat` cohérent avec l'intention

Une seule question sans réponse écrite : ne pas commiter, demander au user/coordinateur.

## Audit pré-merge

Commandes `git diff` + `grep -c sorry` avant/après + workflow rogue commits : [docs/anti-regression-detail.md](../../docs/reference/anti-regression-detail.md#détection-après-coup-audit-rogue-commits).

## Incident référence

2026-04-24 : commit "Mathlib compilation fixes" a remplacé 9 preuves Arrow.lean par `sorry`, perte d'une semaine de port Lean ; restauration via #527. Détail : [docs/anti-regression-detail.md](../../docs/reference/anti-regression-detail.md#incident-fondateur-2026-04-24-arrowlean).
