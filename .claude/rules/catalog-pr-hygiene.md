# Catalogue & hygiène PR — le catalogue appartient à l'automatisation

S'applique à **tous les agents du cluster CoursIA** (workers `po-*` + coordinateur `ai-01`) qui ouvrent des PR. Source : mandat user 2026-06-06 (« régler définitivement le pb du catalogue et faire faire aux agents workers le travail t'économisant le tien »). Codifie la leçon `stale-catalog-silent-revert` (incidents #2376 / #2383 / #2385). **Détecté par CI** : `catalog-drift.yml` (check `Notebook catalog drift (read-only)`, non-bloquant) signale toute PR touchant le catalogue ; la régénération est portée par `catalog-cron.yml` (PR permanente). Le garde bloquant `catalog-pr-guard.yml` a été retiré (#11012) : entité fantôme, 0 run `pull_request` sur ~925 runs `push` en échec. See #2632.

## Règle HARD 1 — NE JAMAIS régénérer le catalogue sur une branche feature

`COURSE_CATALOG.generated.json`, `COURSE_CATALOG.generated.md` et les blocs `<!-- CATALOG-STATUS:START -->…:END -->` dans les README **sont des artefacts générés appartenant à l'automatisation**. Un agent ne les régénère **jamais** à la main sur une branche.

**Pourquoi** : le catalogue embarque des champs git-dérivés (`last_validation`, `issue_pr_associee`, …) + une heuristique de maturité qui **dérivent avec le temps** au fil des commits sur `main`. Régénérer sur une branche dont la base est ancienne produit un diff massif (1000+ lignes) qui mélange des entrées **sans rapport** avec le livrable → conflit catalogue à chaque merge, revert silencieux des champs curés des autres entrées, et explosion de tokens côté coordinateur pour démêler (`git merge origin/main` + de-churn manuel, un par PR).

**Qui régénère, alors** :
- `.github/workflows/catalog-cron.yml` — **cron quotidien** (schedule 03:37 UTC) qui régénère `.json` + `.md` + marqueurs + curriculum + health-dashboard, **sur une branche longue `chore/catalog-refresh-pending`**, commit par `github-actions[bot]`, et ouvre/pingue **une PR permanente** vers `main`. Le bot ne pousse **jamais** directement sur `main` (le `PR gate` requis par la protection de branche est incompatible avec un déclencheur `schedule:` — voir #10136, run 31293765051 du 2026-08-09T04:03Z). C'est le backstop canonique.

  **Le commit du bot ne porte plus `[skip ci]`** (retiré par #10425, cf. #10421) : il le portait, et c'est précisément ce qui rendait le véhicule permanent **immergeable** — une tête sans check ne satisfait jamais le `PR gate`, donc la PR ne pouvait pas être mergée sans un geste manuel de réveil. Le marqueur avait été mis pour éviter que le cron ne se redéclenche lui-même ; il a été payé au prix d'une PR bloquée. Si une `chore/*-pending` se présente malgré tout avec un rollup quasi vide, le geste de réveil est un `gh pr update-branch` (ou un commit vide) sur la branche : il produit une nouvelle tête et déclenche les checks — mesuré sur #10348, 5 → 27 checks.
- `.github/workflows/catalog-drift.yml` — **par-PR**, auto-régénère et committe le catalogue sur la branche d'une PR same-repo (préserve les champs curés via `_merge_curated_fields`, #2433).
- `.github/workflows/translation-sync.yml` — variante pour les **traductions dérivées** (CSV + `*_<lang>.ipynb`), même motif longue-durée : `chore/translation-sync-pending` + PR permanente, post-merge delivery (cf. #10133, #10136).

**Ce que fait l'agent à la place** : laisser le catalogue **byte-identique à `main`**. Si une branche a malgré tout du churn catalogue (régén accidentelle, base stale) :

```bash
git checkout origin/main -- COURSE_CATALOG.generated.json COURSE_CATALOG.generated.md
# puis re-checkout origin/main sur les README dont SEULS les marqueurs CATALOG-STATUS ont bougé
```

Une **nouvelle entrée** notebook (nouveau notebook ajouté) n'est PAS à inscrire à la main : le cron (`<24h`) ou la CI par-PR la crée. Si l'inscription immédiate est nécessaire, la confier à la lane catalog-drift (po-2023), **pas** la régénérer dans une PR de contenu.

**PR permanente (`chore/<name>-pending`) — modèle de livraison du bot (issue #10136)** : ces branches longues sont la propriété de l'automatisation, **pas** des agents. Si tu vois une `chore/catalog-refresh-pending` ou `chore/translation-sync-pending` pointer un commit récent que tu n'as pas écrit, **ne pas la réutiliser comme base d'une PR de contenu** — elle sera re-pushée / re-pinguée par le cron avant que ta PR ne passe le `PR gate`, et ton diff se fera piétiner. Pour modifier le code de `catalog-cron.yml` / `translation-sync.yml` : nouvelle branche `feature/<sujet>` à part, le cron n'y touche pas.

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
