---
name: coordinate
description: Cycle de coordination ai-01 (coordinateur UNIQUEMENT — jamais sur un worker). Lit memoire + dashboards + inbox + GitHub, merge les PRs pretes, tranche les design-gates, dispatche des grains par lane, reporte. Arguments: [--dispatch] [--focus <topic>]
---

# Skill: Coordinate - Cycle coordinateur ai-01

Cycle de coordination du cluster CoursIA. **Reserve au coordinateur ai-01** : un worker ne lance JAMAIS `/coordinate` (lecon #1502 phantom-merger — le cron worker execute `/continue`). Un worker ne merge pas et ne fait pas de `gh auth switch`.

**Target**: `$ARGUMENTS`

## Arguments

- (sans args) : cycle complet (briefing + merges + steers + reporting)
- `--dispatch` : forcer une passe de dispatch explicite vers les lanes idle
- `--focus <topic>` : concentrer le cycle sur un sujet (texte libre : lean, genai, qc, renum, ...)

## Process

### Phase 1 - Contexte memoire

1. `~/.claude/projects/d--CoursIA/memory/MEMORY.md` — index + quick reference
2. `~/.claude/projects/d--CoursIA/memory/coordinator-durable-state.md` — axes directeurs, bloqueurs user, watches, calendrier
3. Au besoin : [docs/reference/cluster-agents.md](../../../docs/reference/cluster-agents.md) (machines, lanes, GPU), [docs/reference/teaching-context.md](../../../docs/reference/teaching-context.md) (calendrier ecoles)

### Phase 2 - Etat live

0. **Rester courant** : `git checkout main && git pull --ff-only` + `git submodule update --init` — le coordinateur travaille sur un main LOCAL a jour, jamais en grepant un working-tree stale ni en pilotant via `origin/*`.
1. **Dashboards (canal PRINCIPAL) — lire LES DEUX, independamment** : `roosync_dashboard(action:"read", type:"workspace", section:"all")` pour `workspace-CoursIA` **et** pour `workspace-CoursIA-2`. Deux lanes co-egales ; **aucune n'est "le dashboard du coordinateur"**. Une `lane` = machine x workspace : chaque machine avec une lane CoursIA-2 a AUSSI une lane CoursIA. Lire chacun separement pour ne rater aucun ASK/blocker.
2. **Inbox DM** : `roosync_messages(action:"inbox", status:"unread")` — les reponses/escalades workers arrivent la.
3. **GitHub** : `gh pr list --state open` (a merger) + `gh issue list --state open --limit 30` (pool).
4. **Cron** : `CronList` — si le job coordinateur a disparu (session-only), re-armer `CronCreate("13 0-23/4 * * *", "/coordinate", recurring)`. Cadence unique, PAS de 2e cron ni ScheduleWakeup en plus.

### Phase 3 - Passe de merge (avant tout dispatch)

Pour chaque PR ouverte, dans l'ordre d'anciennete :

1. Lire body + comments + reviews + diff ([regle HARD](../../../CLAUDE.md) "Read Body Before Any Action").
2. Verifier l'etat A L'INSTANT-T : `gh pr view N --json state,mergedAt,mergeStateStatus` (jamais depuis le dashboard ou le cycle N-1 — lecon phantom-steer #5563).
3. Gates : H.4 (notebooks : checkout + Papermill local OU log dans le body), catalogue byte-identique a main (`gh pr view N --json files` — lecon stale-catalog), scope reel = titre, criteres [pr-review-discipline](../../rules/pr-review-discipline.md).
4. Merge : compte `jsboige` (defaut, seul compte avec MergePullRequest), `--squash` par defaut, `--merge` (preserve-SHA) pour la base d'un stack, **JAMAIS `--delete-branch`**.

### Phase 4 - Steers et design-gates

Regles completes : [coordinator-discipline.md](../../rules/coordinator-discipline.md) (R3 lanes independantes, R4 jamais sanctionner l'idle, R5 steer qui ATTEINT/VRAI/DECIDE).

1. **Trancher les design-gates en attente** dans le cycle — ne pas deferer une option deja investiguee.
2. **Grounder chaque grain firsthand** (`gh issue view N` / `gh pr view N`) AVANT de dispatcher — jamais depuis un status condense.
3. **Double canal obligatoire** : DM `roosync_messages(action:"send", to:"<machine>:<workspace>", subject:"...", body:"...", priority:"HIGH|MEDIUM")` (le worker lit l'inbox en premier, le DM survit a la condensation) **+** pointeur `[DISPATCH→inbox]` sur le dashboard de la lane (sonnette persistante).
4. Une lane sans grain = echec coordinateur : deep-queue, fallback perenne par famille, ou pool global — jamais un statut terminal-idle.

### Phase 5 - Fin de cycle (obligatoire)

1. **Commit + PR AVANT le rapport** — ne jamais annoncer un travail non commite.
2. `[DONE]` lane-specific sur **les deux** dashboards (jamais un miroir copie-colle).
3. **Bloqueurs user** : re-poke explicite dans vscode a CHAQUE fin de session tant que l'action user n'est pas faite ([user-blocker-signaling](../../rules/user-blocker-signaling.md)).
4. MAJ `coordinator-durable-state.md` si l'etat durable a change (PR#/SHA ephemeres → dashboard, pas la memoire).

## Regles importantes

- **Jamais de force push** — cf [git-workflow.md](../../rules/git-workflow.md)
- **Coordination via RooSync uniquement** — aucun fichier de coordination/rapport dans git
- **Deux dashboards workspace, coordonnes independamment** — `workspace-CoursIA` et `workspace-CoursIA-2` sont co-egaux ; lire et poster un contenu lane-specific sur CHACUN a chaque cycle, jamais de broadcast miroir, jamais "le mien vs celui des workers".
- **Issues + PRs** — chaque tache = issue, chaque livraison = PR avec review
- **Priorites courantes** : vivre dans `coordinator-durable-state.md` (memoire) + dashboards — pas dans ce fichier (harness-hygiene : le skill decrit le processus, pas l'etat).
