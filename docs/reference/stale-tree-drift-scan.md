# Scan de drift sur worktree frais (anti-phantom)

Procédure transverse aux workers `po-*` : **toute détection de drift** (traduction `check_translation_sync.py`, nbformat ids, sorry-count, readémie §E) **doit s'exécuter sur un worktree frais syncé `origin/main`**, jamais sur l'arbre partagé `main` local.

## Le piège (symptôme)

Un scanner de drift lancé sur l'arbre partagé (`C:/dev/CoursIA`) rapporte **des dizaines voire centaines de faux positifs** — des anomalies qui n'existent pas sur `origin/main`. Exemple réel, cycle po-2024 (2026-07-15) :

| Source | Anomalies détectées | Vraies (worktree frais) | Faux positifs |
|--------|---------------------|--------------------------|---------------|
| Arbre partagé (dirty, 9 fichiers) | **208** | 26 | **182 (88 %)** |
| Worktree frais `origin/main` | **26** | 26 | 0 |

Le même scanner, sur le même instant, donne **8× plus d'anomalies** sur l'arbre partagé que sur un worktree frais. Un worker qui traite les 208 à l'aveugle fabrique du travail inexistant (un workers a déjà proposé une PR de « résync » sur un dossier en réalité propre).

## Cause mécanique

1. L'arbre partagé est fréquemment **dirty** (WIP Lean d'une session voisine, `.lake` caches, submodules, fichiers générés).
2. `git pull --ff-only` **échoue** sur un arbre dirty (`error: cannot pull with rebase: You have unstaged changes`) → le `main` local **ne se resynchronise pas** avec `origin/main`.
3. Le `main` local reste à un commit ancien pendant que `origin/main` avance (catalog-cron auto-regen, merges ai-01, PRs d'autres workers).
4. Le scanner compare les notebooks/CSV **courants** (qui avancent avec `origin/main`) à un **pivot CSV / référence** lu dans le `main` local **stale** → tout ce qui a avancé entre les deux est vu comme « drift ».

Le phantom grossit avec le temps écoulé depuis la dernière sync de l'arbre partagé.

## Procédure correcte

### Option A — worktree frais (recommandé pour livrer une PR)

```bash
git worktree add ../CoursIA-<sujet> -b <branch> origin/main
cd ../CoursIA-<sujet>
# lancer le scanner ICI (sur l'arbre frais, syncé origin/main)
py -3.13 scripts/translation/check_translation_sync.py translations/ --check
```

Le worktree hérite d'un `main` à jour (checkout depuis `origin/main`), propre, isolé du WIP d'autrui. C'est le seul endroit où un drift détecté est **réel**.

### Option B — lecture directe `origin/main` (pour un audit read-only sans PR)

Pour comparer un fichier à la version canonique sans worktree :

```bash
# drift CSV : scanner un dossier extrait depuis origin/main
git show origin/main:translations/<famille>/<famille>.csv > /tmp/canon.csv
# nbformat ids, sorry-count : lecture depuis origin/main
git show origin/main:<chemin/notebook.ipynb>
```

La référence **doit** provenir de `origin/main`, pas de l'arbre partagé.

## Vérification croisée (lecture directe G.1)

Avant de traiter une anomalie détectée, confirmer qu'elle est réelle :

1. La même anomalie **doit** apparaître sur le worktree frais (option A).
2. Au besoin, lire la cellule/notebook directement (`git show origin/main:...`) pour confirmer le drift source-vs-pivot.

Une anomalie qui n'apparaît que sur l'arbre partagé = **phantom**, ignorer.

## Preuves accumulées (trans-cycle, po-2024)

- **c.487** (Planners) : shared 208 anomalies → worktree frais 24 réelles.
- **c.491** (Probas/Infer) : shared 208 → worktree frais 25 (183 phantom, 88 %).
- **c.493** (Sudoku) : shared 50 → worktree frais 18 (32 phantom, 64 %).
- **c.495** (capture live, ce doc) : shared 208 → worktree frais 26 (182 phantom, 88 %).

Le taux de faux positifs oscille entre 64 % et 88 % selon l'âge de l'arbre partagé. **Toujours scanner sur worktree frais.**

## Anti-pattern

- Lancer `check_translation_sync.py` sur `C:/dev/CoursIA` directement, voir 200 anomalies, et ouvrir 12 PRs de resync sur des familles en réalité propres → fabrication de travail (incident observé c.487).
- « Le scanner dit drift, donc drift » sans vérifier sur worktree frais = propager un claim non vérifié (violation G.1).

## Voir aussi

- [procedures-recurrentes.md](procedures-recurrentes.md) — workflow PR + validation notebook
- [sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md) — vérifier claims contre la source (G.1)
- Issue [#4957](../../../issues/4957) — infra de synchro traduction (le scanner `check_translation_sync.py`)
