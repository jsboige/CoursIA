# Catalogue & hygiène PR — le catalogue appartient à l'automatisation

S'applique à **tous les agents du cluster CoursIA** (workers `po-*` + coordinateur `ai-01`) qui ouvrent des PR. Source : mandat user 2026-06-06 (« régler définitivement le pb du catalogue et faire faire aux agents workers le travail t'économisant le tien »). Codifie la leçon `stale-catalog-silent-revert` (incidents #2376 / #2383 / #2385). **Enforcé par CI** : `catalog-guard.yml` FAIL toute PR touchant le catalogue (exception : bot `github-actions[bot]`). See #2632.

## Règle HARD 1 — NE JAMAIS régénérer le catalogue sur une branche feature

`COURSE_CATALOG.generated.json`, `COURSE_CATALOG.generated.md` et les blocs `<!-- CATALOG-STATUS:START -->…:END -->` dans les README **sont des artefacts générés appartenant à l'automatisation**. Un agent ne les régénère **jamais** à la main sur une branche.

**Pourquoi** : le catalogue embarque des champs git-dérivés (`last_validation`, `issue_pr_associee`, …) + une heuristique de maturité qui **dérivent avec le temps** au fil des commits sur `main`. Régénérer sur une branche dont la base est ancienne produit un diff massif (1000+ lignes) qui mélange des entrées **sans rapport** avec le livrable → conflit catalogue à chaque merge, revert silencieux des champs curés des autres entrées, et explosion de tokens côté coordinateur pour démêler (`git merge origin/main` + de-churn manuel, un par PR).

**Qui régénère, alors** :
- `.github/workflows/catalog-cron.yml` — **cron quotidien sur `main`** (régén `.json` + `.md` + marqueurs, commit `[skip ci]` par `github-actions[bot]`). C'est le backstop canonique.
- `.github/workflows/catalog-drift.yml` — **par-PR**, auto-régénère et committe le catalogue sur la branche d'une PR same-repo (préserve les champs curés via `_merge_curated_fields`, #2433).

**Ce que fait l'agent à la place** : laisser le catalogue **byte-identique à `main`**. Si une branche a malgré tout du churn catalogue (régén accidentelle, base stale) :

```bash
git checkout origin/main -- COURSE_CATALOG.generated.json COURSE_CATALOG.generated.md
# puis re-checkout origin/main sur les README dont SEULS les marqueurs CATALOG-STATUS ont bougé
```

Une **nouvelle entrée** notebook (nouveau notebook ajouté) n'est PAS à inscrire à la main : le cron (`<24h`) ou la CI par-PR la crée. Si l'inscription immédiate est nécessaire, la confier à la lane catalog-drift (po-2023), **pas** la régénérer dans une PR de contenu.

## Règle HARD 2 — Rebase frais avant push

Repartir d'un `origin/main` à jour avant de pousser. Le label `base-stale-14d` (workflow `stale-base-warning.yml`) signale une base de plus de 14 jours en retard → re-baser **avant** de demander un merge. Une branche stale = source n°1 du poison catalogue ci-dessus + de conflits inutiles.

## Règle HARD 3 — Un seul livrable par PR (atomique)

Une PR = **un** sujet vérifiable (cf G.4 / one-subject-per-PR). Pas de composite « 4 notebooks + refactor script + docs » : split. Seuils CHANGES_REQUESTED : > 3000 lignes hors notebooks / > 15 fichiers / > 4 features / > 1 domaine ([pr-review-discipline.md](pr-review-discipline.md) §A).

## Règle HARD 4 — `Closes #X` quand la PR résout entièrement l'issue

- **`Closes #X` / `Fixes #X`** dans le body **uniquement** quand UNE PR résout **entièrement** UNE issue → GitHub la ferme automatiquement au merge (le backlog d'issues diminue tout seul).
- **`See #X` / `refs #X`** pour une **contribution partielle** à une epic (l'epic reste ouverte). Ne PAS utiliser `Closes` sur une sous-tâche d'epic.

Cette discipline est ce qui fait **baisser le compte d'issues** sans intervention manuelle du coordinateur : une PR qui clôt vraiment une issue le déclare, les epics au long cours restent `See`.

## Voir aussi

- [.claude/rules/git-workflow.md](git-workflow.md) — branches `feature/`, no force push, no direct main push
- [.claude/rules/proactive-coordination.md](proactive-coordination.md) — 1 PR/wakeup, atomique
- [.claude/rules/pr-review-discipline.md](pr-review-discipline.md) — §A composites trop larges
- `~/.claude/projects/d--CoursIA/memory/stale-catalog-silent-revert.md` — incident fondateur
