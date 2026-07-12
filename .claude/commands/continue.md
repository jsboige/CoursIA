# Continue - Cycle worker

Reprendre le travail sur cette lane : lire les directives coordinateur, choisir la prochaine tache, livrer une PR, reporter. C'est le prompt du cron worker (30 min staggered). **Un worker ne lance JAMAIS `/coordinate`** (lecon #1502) : pas de merge, pas de `gh auth switch`, pas de close d'issue d'autrui.

## Workflow

### Phase 1 : Contexte (30s)

1. Lire `MEMORY.md` (auto-memory) pour l'etat des sessions precedentes
2. `git checkout main && git pull --ff-only` — repartir d'un main courant (les branches feature se rebasent frais, cf [catalog-pr-hygiene](../rules/catalog-pr-hygiene.md))
3. `git status` — si l'arbre partage est sale (WIP d'une autre session), travailler en **worktree isole** : `git worktree add ../CoursIA-<sujet> -b feature/<sujet> origin/main`. Ne jamais stasher/toucher le WIP d'autrui.

### Phase 1.5 : Tour RooSync (obligatoire, AVANT de travailler)

1. **Inbox DM en PREMIER** : `roosync_messages(action:"inbox", status:"unread")` — le DM est le canal de decision du coordinateur, il survit a la condensation du dashboard.
2. **Dashboard workspace** : `roosync_dashboard(action:"read", type:"workspace", section:"all")` — chercher les `[DISPATCH→inbox]` et les steers de MA lane (`machine:workspace`). Si la machine a une lane CoursIA-2, lire aussi ce dashboard pour cette lane.
3. **Filtrage workspace** : traiter UNIQUEMENT les messages adresses a cette lane ou cette machine ; ignorer les autres workspaces.
4. Missions coordinateur (ai-01) HIGH/URGENT = priorite sur les taches locales. Accuser reception (reply DM ou dashboard).

### Phase 2 : Choisir la tache

**P0 — Missions coordinateur** : DM HIGH/URGENT, puis steers dashboard de ma lane.

**P1 — Travail en cours** : tache `[CLAIMED]` par cette lane non terminee, deep-queue de la lane si posee sur le dashboard.

**P2 — Pool global (auto-alimentation, JAMAIS d'idle)** : `gh issue list --state open` **en entier, cross-lane** — la lane est une etiquette de reporting, pas une frontiere de travail. Prendre n'importe quelle issue techniquement executable (autre famille, autre langage : rien n'est "le turf d'un autre"), poser `[CLAIMED] <#N> — <machine:workspace> <ts>` sur le dashboard AVANT de commencer, livrer. Regles completes : [proactive-coordination.md](../rules/proactive-coordination.md) (>=1 PR/wakeup = PLANCHER, variete R6, "rien a faire" avec >0 issues ouvertes = echec de methode).

### Phase 3 : Travailler et livrer

- Une PR = un sujet ([catalog-pr-hygiene](../rules/catalog-pr-hygiene.md) : catalogue byte-identique a main, `Closes #N` seulement si l'issue est entierement resolue, sinon `See #N`).
- Notebooks : C.1 (pas d'erreur volontaire), C.2 (commit AVEC outputs, re-exec des cellules modifiees), H.3 (pre-commit) — cf [notebook-conventions.md](../rules/notebook-conventions.md).
- Vrai outil SOTA, jamais workaround degrade ([sota-not-workaround.md](../rules/sota-not-workaround.md)) ; env casse = reparer, pas contourner (regle F).
- Skills/sous-agents specialises quand ils existent : [docs/reference/subagents-reference.md](../../docs/reference/subagents-reference.md).

### Phase 4 : Avant de terminer (obligatoire)

1. **Commit + PR AVANT le rapport** — jamais de [DONE] sur un travail non commite.
2. `[DONE]` lane-specific sur le dashboard workspace (resume : livrable, PR#, residuel). Une PR livree ne clot pas la session : re-piocher si la fenetre le permet.
3. Bloqueur necessitant une action user : tag `[ASK USER]` separe du [DONE], repete a CHAQUE fin de session ([user-blocker-signaling](../rules/user-blocker-signaling.md)).
4. Repondre au DM coordinateur si une mission a ete traitee.
5. MAJ `MEMORY.md` si lecon durable (les PR#/SHA ephemeres vont au dashboard, pas en memoire).

## Notes

- Commande **sans parametre** : elle choisit automatiquement la tache suivante.
- Etat persistant : dashboards RooSync + issues GitHub + MEMORY.md.
- Jamais d'etat terminal-idle ("rien a faire", "await dispatch", "lane exhausted") : le pool global est toujours ouvert.
