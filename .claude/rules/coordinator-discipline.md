# Coordinator discipline — merge actively, no languishing requests

S'applique au **coordinateur ai-01** (`myia-ai-01:CoursIA`).

Detail complet (workflow batch merge + commandes + audit pre-merge + incidents + verbatims + mapping lanes + listes de rollout + 4-mecanismes de chaque regle) : [docs/secrets-and-coord-detail.md §2](../../docs/reference/secrets-and-coord-detail.md#2-coordinator-discipline-ai-01).

## Regle 1 : ai-01 merge soi-meme via `gh auth switch`

Le compte `myia-ai-01` n'a **pas** le droit `MergePullRequest` (GraphQL) sur `jsboige/CoursIA`. Le compte `jsboige` (token scopes `repo workflow`) a les droits.

Quand 1+ PR(s) CLEAN MERGEABLE + APPROVED s'accumulent : `gh auth switch -u jsboige` → merge → `gh auth switch -u myia-ai-01` → post dashboard ack. **Pas** de "pending user merge" dans le todo. Ne pas confondre "permissions GitHub absent" avec "interdiction de merger". User feedback 2026-05-19 : "Fais un switch pour merger toi meme stp".

**Exception** : PR notebook → regle H.4 (`git checkout` + Papermill local + verify `execution_count`) AVANT merge.

## Regle 2 : aucune demande user ne pourrit > 1 cycle

Quand le user formule une demande concrete et realisable :
- **< 30 min, action locale** : executer dans la session courante.
- **30 min - quelques heures** : creer immediatement dispatch + post dashboard `[INFO]` + acker user au tour suivant.
- **Multi-day** : creer immediatement GitHub issue avec scope + acceptance + label + ack user.

**Interdits** : "je note pour prochain cycle" sans tracking concret (issue/dispatch/dashboard line) ; recycler la demande via des `MEMORY.md` updates sans action ; attendre que user re-formule.

**Verification fin de session** : avant `[DONE]`, parcourir les N derniers messages user et confirmer que chaque demande a soit (a) ete executee, (b) eu un dispatch trace, (c) eu une issue ouverte, (d) ete reportee avec justification ecrite acceptee. Reflexe G.9 : "qu'est-ce que le user a demande que je n'ai pas encore fait ?" > "qu'est-ce qui reste dans mon plan ?".

## Regle 3 : coordonner CHAQUE lane independamment (HARD)

**Deux dashboards workspace co-egaux** : `workspace-CoursIA` et `workspace-CoursIA-2`. **Aucun n'est "le dashboard du coordinateur"**. Un `lane` = **machine x workspace** ; chaque worker avec une lane CoursIA-2 a **AUSSI** une lane CoursIA.

Chaque cycle `/coordinate` : **LIRE `section:"all"` sur LES DEUX** (sinon les ASKs/blockers d'une lane restent invisibles) **et POSTER un contenu lane-specific sur LES DEUX** — **jamais de broadcast miroir** (copier-coller identique), jamais traiter l'un comme « le mien » et l'autre comme « celui des workers ». Surveiller la **duplication cross-lane** (un worker peut dedoubler une livraison sur ses deux lanes → reconcilier : 1 canonique mergee, l'autre disposee).

Mapping lanes + incident fondateur (mandat 2026-06-14) : [§2.3](../../docs/reference/secrets-and-coord-detail.md#2-coordinator-discipline-ai-01).

## Regle 4 : JAMAIS sanctionner une lane idle — deep-queue + fallback perenne (HARD)

S'applique **meme quand ai-01 est mobilise par le user** sur une autre tache. Une lane idle = **echec ai-01**, jamais un etat worker acceptable.

- **Interdit de sanctionner l'idle** : ne JAMAIS poster un statut terminal-idle (« honest-idle legit », « lane exhausted/closed », « await dispatch » comme etat final).
- **Deep queue** = ~5-10 steps ordonnes par lane sur le dashboard, assez profonde pour plusieurs cycles meme si ai-01 est absent. Pre-autorisation : « brule-les dans l'ordre, ne m'attends PAS entre steps, ASK seulement sur blocker reel ou queue vide ».
- **Fallback perenne never-empty par famille** : quand la deep-queue est epuisee, le worker tombe sur le rollout repo-wide famille-partitionne de SA famille. **Un tracker FERME ne ferme pas le rollout** — ne jamais lire « issue closed » comme « fallback indisponible ». `[CLAIMED] <item> — <machine:workspace> <ts>` avant de commencer. Quand un tracker LIVE ferme, le remplacer par son successeur OPEN.
- **Token economy = Anthropic-only** ([[feedback-token-economy-anthropic-only]]) : ne ferme JAMAIS une lane Lean/research sur workers z.ai/GLM/MiniMax. ai-01 ne valide pas un HOLD Lean motive par l'economie.

Incident 2026-06-16 (verbatim) + liste des rollouts LIVE (#3973 + filles, #4212, #3870, #2876, #2161) : [§2.4](../../docs/reference/secrets-and-coord-detail.md#2-coordinator-discipline-ai-01). Voir aussi [[never-close-a-lane-feed-deep-queue]], [[feedback-dispatch-fill-spare-capacity]].

## Regle 5 : le STEER doit ATTEINDRE le worker, etre VRAI, et DECIDER (HARD)

**L'idle est un echec COORDINATEUR, jamais worker** (renforce Regle 4). Un steer poste seulement sur l'intercom (qui auto-condense/archive chaque cycle), redige depuis un status condense qui hallucine, ou qui defere les design-gates = **phantom** : le worker brule ses cycles a le refuter au lieu de produire. Chaque cycle, par lane :

1. **DIRECT MESSAGE** (`roosync_messages send`/`reply` vers `machine:workspace`), pas seulement un append dashboard — le worker lit `inbox status:unread` en premier, et le DM survit a la condensation. Dashboard = backstop persistant + sonnette `[DISPATCH→inbox]`, pas le canal de decision.
2. **Grounder chaque grain firsthand AVANT de dispatcher** (`gh issue view N` / `gh pr view N`), jamais depuis le status condense. Un steer qui pointe une issue CLOSED / une PR mergee / un rollout sature = phantom. Worker firsthand-sature → **le croire**, fournir un grain HORS scope.
3. **DECIDER les design-gates, ne pas deferer** : greenlight nomme + acceptance dans le cycle. Deferer une option deja investiguee = fabriquer de l'idle.
4. **Familles matures = fallback perenne epuisable** → deux sources never-empty le remplacent : **(a) CREATION SUBSTANTIELLE** scopee-coordinateur (nouveaux lakes Lean, audits axe-2 SOTA, consolidation, notebooks) stockee en avance ; **(b) DIVERSITE DU BACKLOG en souffrance** — piocher **une tranche concrete** par cycle de vieilles issues/EPICs, varier genres ET familles, jamais tunneliser un mono-theme.

**Tell d'auto-detection** avant de poster un steer : « (a) grain verifie OPEN/non-sature firsthand a l'instant ? (b) la decision atteint-elle l'inbox du worker ? (c) ai-je tranche, ou defere ? » — trois oui requis, sinon phantom.

Mandat 2026-06-26 (verbatim) + listes d'issues des sources (a)/(b) : [§2.5](../../docs/reference/secrets-and-coord-detail.md#2-coordinator-discipline-ai-01). Voir aussi [[verify-before-claiming]], [[diversity-backlog-aged-issues]], [[feedback-double-dm-with-dashboard-notif]].

## Voir aussi

- [proactive-coordination.md](proactive-coordination.md) — 1 PR/wakeup plancher, backlog pickup 8 sources, queue profonde
- [git-workflow.md](git-workflow.md) — branches feature/, no force push
- [pr-review-discipline.md](pr-review-discipline.md) — Critere CHANGES_REQUESTED
- CLAUDE.md section A — ai-01 review et merge, agents ne mergent pas
- CLAUDE.md section H.4 — Merges coord JAMAIS complaisants
