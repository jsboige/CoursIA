# Review-coverage threshold — pourquoi 300, comment l'ajuster

Document de support pour l'organe [`scripts/review_coverage.py`](../../scripts/review_coverage.py)
et le workflow [`.github/workflows/review-coverage-advisory.yml`](../../.github/workflows/review-coverage-advisory.yml).
Source : issue **#11232** (review-coverage), mandat 2026-08-16.

## Le problème

Hermes et ai-01 lisent `reviews[]` et les trois surfaces de B.0 de
[`pr-review-discipline.md`](../../.claude/rules/pr-review-discipline.md). Aucun
de ces gestes ne détecte **l'absence** de review. Une PR sans review et sans
réserve ouverte lit vert sur tous les signaux visibles : `gh pr checks` 0
failures, 0 pending, `mergeable: MERGEABLE`, `reviews[].state` vide.

**Mesure firsthand 2026-08-16** sur la fenêtre Lean :

| PR      | additions | reviews      | signal déclenché                                |
|---------|-----------|--------------|--------------------------------------------------|
| #11132  | 1041      | 0            | **aucun** (silence sur tous les indicateurs)     |
| #11210  | 883       | 0            | **aucun** (silence sur tous les indicateurs)     |
| #11217  | 318       | 2 (Hermes + ai-01) | `second-reviewer` (parce qu'il y a 1 review) |
| #11048  | 425       | 1 (Hermes)   | review présente, OK                            |

Les deux plus grosses PRs de la fenêtre — **#11132 et #11210** — n'avaient
**aucune review** au moment où elles ont été mergées. Le seuil `second-reviewer`
(200 LOC) a été déclenché par Hermes **uniquement** sur #11217 (qui avait
**déjà** 1 review : ai-01). Le seuil de Hermes **exigeait** une review, et
les PRs qui n'en avaient **aucune** étaient littéralement invisibles.

## Le seuil de l'organe

**Défaut : 300 additions.** Argumentation :

- **Au-dessus de 300** : capture #11132 (1041) et #11210 (883), les deux
  exemples motivants. Justifie l'organe.
- **En dessous de 300** : la PR #11217 (318) avec 2 reviews reste visible
  par sa review, pas par le label. Pas de concurrence entre les deux
  organes.
- **300 vs 200** : Hermes applique 200. Pourquoi 300 ici ? L'organe
  `review-coverage` est **fréquent** (cron quotidien) et **labellisant**
  (le label se voit). Un seuil à 200 ferait flamber le dashboard. 300
  est la limite haute qui distingue encore la couverture manquante d'une
  PR dense mais relue.

## Historique

| Date       | Qui | Décision | Justification |
|------------|-----|----------|---------------|
| 2026-08-16 | Hermes | 200 LOC (`second-reviewer`) | seuil humain, sur une PR précise |
| 2026-08-16 | ai-01 | 300 LOC (défaut `review-coverage`) | seuil cron, label visible, frequency quotidienne |
| 2026-08-17 | po-2024 | 300 (implémentation) | match le défaut décisionnel, ajustable par CLI |

## Comment changer le seuil

Deux mécanismes, **sans toucher au code** :

1. **Workflow dispatch** (one-shot, pour un test) : Actions → "Review coverage
   advisory" → Run workflow → champ `threshold` (default 300).
2. **Cron** (permanent, nécessite un edit du YAML) : modifier la ligne
   `python scripts/review_coverage.py $DRY --threshold 300 --label ...` dans
   [`.github/workflows/review-coverage-advisory.yml`](../../.github/workflows/review-coverage-advisory.yml).
   À faire dans une PR dédiée `chore(review-coverage): bump threshold to NNN`.

## Exceptions documentées

- **Draft PRs** : exclues par construction (`isDraft=True` → `skip_draft`).
  Une PR en draft est par construction non-prête, label = bruit.
- **Base ≠ main** : exclues par construction. Le label est un signal du
  coverage hole **de la piste principale** (main-track). Une PR vers
  `feature/foo` a une audience de revue différente (le propriétaire de
  la branche, les co-workers).
- **Reviews de bot** : **comptent**. Une review de `clusterManager-Myia`
  lève le label. Exclure les bot reviews recréerait le trou sur une
  surface plus étroite (incident fondateur documenté dans le docstring
  de `classify`).

## Pourquoi ADVISORY et pas bloquant

L'organe **ne peut pas** bloquer : le défaut est l'**absence** de review, et
le seul remède est **obtenir une review**. Un check bloquant ferait deux
choses rédhibitoires :

1. **Bloquer le merge** d'une PR non-reviewée alors que la **vraie**
   solution est d'**obtenir** une review, pas de bloquer.
2. **Ne pas bloquer** quand la review arrive, et donc **ne pas** apprendre
   aux auteurs à demander une review en amont.

L'organe label et commente. Le commentaire nomme l'action (`obtenir une
review`) et explique pourquoi close/reopen ne suffit pas. Le label est
**retiré** dès qu'une review arrive (current-state flag, pas sticky).

## Conformité

- **G-VAR-1** : le grain est `MED/guard` (plancher **DEEP/MED CONTENU**
  est satisfait par le pivot anterior — c.1331p241 = DEEP/notebook-python).
- **claim-paths-verify** (c.1331p233 ★★★) : paths déclarés au claim :
  `scripts/review_coverage.py`, `.github/workflows/review-coverage-advisory.yml`,
  `docs/reference/review-coverage-threshold.md`. Tous créés dans la PR.
- **catalog-pr-hygiene** : pas de marqueur `CATALOG-STATUS` touché.
- **H.1** : script CLI testé end-to-end (12 cas pytest), dry-run vérifié
  sur la fenêtre locale (no-PR-flagged run pour confirmer que le
  classifier ne bronche pas sur une liste vide).

## Liens

- Issue : https://github.com/jsboige/CoursIA/issues/11232
- PR : https://github.com/jsboige/CoursIA/pull/XXXXX (à compléter)
- Tests : `scripts/tests/test_review_coverage.py` (12/12 fixtures)
- Règle B.0 : [`.claude/rules/pr-review-discipline.md`](../../.claude/rules/pr-review-discipline.md)
- Variation (G-VAR-1/2/3) : [`.claude/rules/variation-protocol.md`](../../.claude/rules/variation-protocol.md)
