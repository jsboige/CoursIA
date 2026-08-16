# Anti-régression : préserver le travail existant

S'applique au **code de production** (preuves Lean/Coq/Agda, fonctions métier appelées, tests, librairies). **Pas** aux cellules d'exercice étudiant — celles-ci doivent justement être stubbées sans `raise NotImplementedError` (cf [notebook-conventions.md](notebook-conventions.md) règle C.1).

**Contexte complet, patterns détaillés par langage, requêtes audit, incidents** : [docs/anti-regression-detail.md](../../docs/reference/anti-regression-detail.md).

## Règle HARD

**INTERDIT** : remplacer une preuve formelle ou une implémentation existante par `sorry` / stub vide / `return None` / `pass`, sans diagnostic explicite et tactiques d'adaptation tentées.

Commits "fix compilation" / "Mathlib fix" / "lint fix" / "simplify" avec **deletions > insertions** sur code métier sont **red flag** par défaut.

## Red-flag rapides

- **Lean/Coq/Agda** : `theorem foo := by <tactics>` → `:= by sorry` = régression. Un compte de `sorry` **réel** qui monte sans justification = PR contestée — mesuré avec `python scripts/lean/count_code_sorry.py --json` (champ `distinct_code_sorry`), **jamais** `grep -c sorry`. Détail de l'instrument ci-dessous.
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

## Compter les `sorry` — un seul instrument, et deux façons de se tromper

```bash
python scripts/lean/count_code_sorry.py --json   # champ distinct_code_sorry
```

Les deux instruments artisanaux échouent, mais **pas de la même façon** — et c'est le second qui est dangereux :

| Instrument | Défaut | Se voit ? |
|---|---|---|
| `grep -c sorry` | **sur-compte** la prose (docstrings, `-- commentaires`, feuilles de route) — 484 naïfs pour 21 réels sur les 21 lakes, mesuré le 2026-08-14 | **oui** : la prose saute aux yeux dès qu'on ouvre le fichier |
| jeu de motifs « code-only » écrit à la main (`:= by sorry`, `^\s*sorry$`, `<;> sorry`) | **sous-compte** : ignore `exact sorry` et `def … := sorry` — rend **2** là où le lake en porte **16** (`knot_lean`, mesuré le 2026-08-16) | **non** : un motif absent ne lève pas d'erreur, il rend un chiffre plus petit et plus propre |

Le second a fait qualifier de « résidu » pendant onze jours le lake portant 80 % de la dette formelle du dépôt. Un motif de détection se valide **par ses faux négatifs** — écrire les formes qu'il doit attraper, vérifier qu'il les attrape — pas par ses hits.

Les paires FR/EN (convention i18n #4980) doublent le compte brut : `distinct_code_sorry` dédoublonne, `code_sorry` non. Un fix se porte **sur les deux siblings**.

## Audit pré-merge

Commandes `git diff` + comptage avant/après (ci-dessus) + workflow rogue commits : [docs/anti-regression-detail.md](../../docs/reference/anti-regression-detail.md#détection-après-coup-audit-rogue-commits).

## Incident référence

2026-04-24 : commit "Mathlib compilation fixes" a remplacé 9 preuves Arrow.lean par `sorry`, perte d'une semaine de port Lean ; restauration via #527. Détail : [docs/anti-regression-detail.md](../../docs/reference/anti-regression-detail.md#incident-fondateur-2026-04-24-arrowlean).
