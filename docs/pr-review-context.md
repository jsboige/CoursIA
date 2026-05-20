# PR Review Discipline — Contexte, incident, anti-patterns

Document de référence détaillant les seuils auto-loaded de [.claude/rules/pr-review-discipline.md](../.claude/rules/pr-review-discipline.md).

## Contexte (incident 2026-05-08)

Règle créée 2026-05-08 après constat user "vous êtes tous trop complaisants, on n'avance pas". Audit cycles 5-7 :
- 9/10 PRs nuit du 7→8 APPROVED par clusterManager-Myia sans contestation
- #801 mega-composite 7183 lignes / 41 files
- #806 +2 lignes
- #807 +46 lignes doc
- #791 du 7/05 +3561/-3543 prover refactor caché derrière "shapley sorry 2→1"

Cette rule s'applique à **tous les reviewers**, humains et bots (clusterManager-Myia, jsboige self-bot, ai-01 coordinateur).

## Anti-pattern : APPROVED en lot batch

Si un reviewer APPROVE >3 PRs dans une fenêtre <10 minutes : flag automatique, probable rubber-stamp.

## Mention explicite des bots

**@clusterManager-Myia** : ces critères s'appliquent en priorité. Première ligne de défense. Si APPROVE une PR violant un des critères, le coordinateur ai-01 conteste explicitement et la PR est bloquée jusqu'au split / fix.

**@jsboige (self-review bot)** : self-approval sans valeur GitHub. Reste en COMMENTED + signale les violations dans le body.

## Workflow ai-01 (coordinateur)

Avant tout merge cascade, ai-01 lit :
1. `gh pr view <N> --json files,additions,deletions,body,reviews` (pas juste `mergeStateStatus`)
2. Vérifie chacun des critères A-G applicables (cf rule)
3. Si violation : commente sur la PR (`gh pr comment <N>`) avec demande explicite (split, multi-seed, sorry-count, etc.) + ne merge pas
4. Si conforme : merge avec mention dans le bilan dashboard

Pas de merge en parallèle 5 PRs sans avoir lu les 5 bodies.

## Détails par critère

### Critère D : preuve d'exécution notebook
- Pas de validation visuelle (PPTX/Slidev) jamais "OK" sur "j'ai screenshotté". Liens vers screenshots obligatoires.
- Sortie `papermill` ou kernel exec — pas juste "Papermill SUCCESS" en mot-clé, coller les premières lignes des outputs.

### Critère E : anti-pattern visé
PRs micro qui inflate le compteur "PRs livrées" sans valeur réelle (#806 +2 lignes, #807 +46 lignes doc seul). Doc/README/CLAUDE.md/rules :
- Single PR < 50 lignes : refuser, exiger groupement avec autre PR du même cycle
- Single PR < 20 lignes : refuser systématiquement (commit direct sur main si trivial)
- Multiple READMEs touchés sans cohérence cross-series : refuser, exiger un seul focus

### Liens internes

- [feedback_multi_seed_required.md](../.claude/memory/feedback_multi_seed_required.md) — pour critère C (ML)
- [feedback_use_bot_reviews_for_dispatch.md](../.claude/memory/feedback_use_bot_reviews_for_dispatch.md)
- [feedback_review_state_filter.md](../.claude/memory/feedback_review_state_filter.md)
- [.claude/rules/anti-regression.md](../.claude/rules/anti-regression.md)
- CLAUDE.md section B (Reviews PR 5 points obligatoires)
