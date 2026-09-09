---
name: coordinate
description: Cycle de coordination ai-01 (coordinateur UNIQUEMENT — jamais sur un worker). Lit memoire + dashboards + inbox + GitHub, merge les PRs pretes, tranche les design-gates, dispatche des grains par lane, reporte. Arguments: [--dispatch] [--focus <topic>]
---

# Skill: Coordinate - Cycle coordinateur ai-01

Cycle de coordination du cluster CoursIA. **Reserve au coordinateur ai-01** : un worker ne lance JAMAIS `/coordinate` (lecon #1502 phantom-merger — le cron worker execute `/continue`). Un worker ne merge pas et ne close pas l'issue d'autrui ; `gh auth switch` est autorise et necessaire (trousseau gh partage entre workspaces — mandat user 2026-08-31) : le switch n'est pas la ligne rouge, le merge/close l'est.

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
3. **GitHub** : `gh pr list --state open` (a merger) + le pool **tire, jamais scanne** — `python scripts/pick_idle_grain.py --lane myia-ai-01:CoursIA` (un `gh issue list` nu plafonne a 30, tries par recence : il ne montre que ce que je viens de creer, et c'est ce biais que le steering doit eviter de reproduire).
4. **Cron** : `CronList` — si le job coordinateur a disparu (session-only), re-armer `CronCreate("13 0-23/4 * * *", "/coordinate", recurring)`. Cadence unique, PAS de 2e cron ni ScheduleWakeup en plus.

### Phase 3 - Passe de merge (avant tout dispatch)

Sweep batche, dossiers prepares en parallele, decision sequentielle au coordinateur — pas de re-audit integral PR par PR.

1. **Sweep leger batche** : `gh pr list --state open --limit 200 --json number,title,author,createdAt,mergeStateStatus,reviewDecision,headRefOid --jq 'sort_by(.createdAt) | .[] | [.createdAt[0:10],.number,.mergeStateStatus,.reviewDecision,.title] | @tsv'` — un seul appel, tri explicite par anciennete (sans `--limit`, gh plafonne a 30 et sans tri declare). Le sweep ordonne et qualifie, il ne decide pas : `mergeStateStatus` / `reviewDecision` restent aveugles aux trois surfaces B.0. **Pas de champ `reviews` dans le sweep** (payload lourd — 504) : les corps detailles (reviews, comments, bodies) se lisent par PR dans les lots de decision (etape 4). Si le rendu atteint 200 lignes, le plafond est touche — paginer plutot que croire la liste complete.
2. **Corps de review Hermes/NanoClaw lus PAR DEFAUT — leur verification est deja faite** : verdicts `[Hermes] COMMENT_WITH_CONCERNS` (prefixe de `reviews[].body`) et `EXEC_PROVED` / `STRUCTURAL_ONLY` / `SUSPECT_REGRESSION` (body). Les exploiter au lieu de rejouer l'audit : le coordinateur ne verifie que (a) le **delta** depuis la derniere review — commits pousses apres, qui ne leve rien par eux-memes (B.0 : une phrase leve, pas un SHA) ; (b) les **reserves non levees** — CONCERNS, `CHANGES_REQUESTED` (le sien non plus ne s'auto-leve pas, #8821), nits user, threads inline non resolus ; (c) la **preuve decisive** du claim central — pas de repetition des tests/audits deja etayes ; la lecture du diff reste requise avant signature. Tout finding NanoClaw suit le protocole [audit-reassessment.md](../../rules/audit-reassessment.md) avant fix (FP connus).
3. **Dossiers en parallele, decision au coordinateur** : les PRs proches de decision partent en preparation `run_in_background: true` chez des sous-agents varies — modele explicite obligatoire, haiku pour le mecanique (comptages, extraction, verification de champs), sonnet pour l'interpretation bornee, cf [model-delegation.md](../../rules/model-delegation.md) — pendant que le coordinateur lit et tranche les dossiers murs. **Le lot de chaque sous-agent est une liste explicite de numeros de PR extraite de la capture unique du sweep (etape 1)** — jamais d'enumeration du pool par le sous-agent lui-meme : des partitions recalculees par agent se recouvrent et dupliquent le travail. Dossier attendu : preuves citees (file:line, log, SHA), verdict par critere [pr-review-discipline](../../rules/pr-review-discipline.md), questions ouvertes. Un dossier insuffisant repart avec UNE question precise et la preuve de sortie attendue — jamais un re-audit integral par reflexe. Un dossier pret remonte immediatement, sans attendre les autres.
4. **Lecture B.0 personnelle avant chaque merge — non delegable** : body + comments + reviews + diff (regle HARD "Read Body Before Any Action", `~/.claude/CLAUDE.md` global) ; etat A L'INSTANT-T via `gh pr view N --json state,mergedAt,mergeStateStatus,reviews` (jamais depuis le dashboard ni le cycle N-1 — lecon phantom-steer #5563) ; organe `python scripts/check_unaddressed_nits.py <PR>` (exit 1 = ne pas merger — son vert ne dispense pas de la lecture). Une levee porte un auteur et une heure.
5. Gates : H.4 (notebooks : checkout + Papermill local OU log dans le body), catalogue byte-identique a main (`gh pr view N --json files` — lecon stale-catalog), scope reel = titre.
6. Merge : directement sous `myia-ai-01` (a le droit `MergePullRequest`, verifie firsthand 2026-08-08 ; `gh auth switch -u jsboige` reserve a la lecture/ecriture de la protection de branche, cf [coordinator-discipline.md](../../rules/coordinator-discipline.md) Regle 1), `--squash` par defaut, `--merge` (preserve-SHA) pour la base d'un stack, **JAMAIS `--delete-branch`**.
7. **Le rouge sans lane est a MOI.** Le garde "reparer son rouge d'abord" ([proactive-coordination](../../rules/proactive-coordination.md) R5) renvoie chaque lane sur ses propres PRs bloquees — mais une PR **sans tag `Grain:` lisible** n'est imputable a aucune lane et reste donc invisible a tous les gardes. Personne ne viendra les reprendre : lire le commentaire marker-guarde `GRAIN-ORPHANS-SWEEP` sur #13086 (balayage quotidien, rafraichi a la demande via `python scripts/pick_idle_grain.py --orphans-report`) et traiter chaque orpheline nommee avec son auteur — reparer, dispatcher nommement, ou fermer en le disant. Le coordinateur est soumis au meme garde pour **sa propre** lane : son tirage lui assigne la reparation de ses propres PRs -- sortie 0, grain rendu -- tant que ses PRs rouges trainent.

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

- **Force push** : jamais sur `main` ; autorisé sur une branche de PR à lane unique — cf [git-workflow.md](../../rules/git-workflow.md)
- **Coordination via RooSync uniquement** — aucun fichier de coordination/rapport dans git
- **Deux dashboards workspace, coordonnes independamment** — `workspace-CoursIA` et `workspace-CoursIA-2` sont co-egaux ; lire et poster un contenu lane-specific sur CHACUN a chaque cycle, jamais de broadcast miroir, jamais "le mien vs celui des workers".
- **Issues + PRs** — chaque tache = issue, chaque livraison = PR avec review
- **Priorites courantes** : vivre dans `coordinator-durable-state.md` (memoire) + dashboards — pas dans ce fichier (harness-hygiene : le skill decrit le processus, pas l'etat).
