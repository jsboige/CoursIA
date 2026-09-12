# Coordinator discipline — merge actively, no languishing requests

S'applique au **coordinateur ai-01** (`myia-ai-01:CoursIA`), **chef de flotte** : management/coordination et merges d'abord ; la minutie est deleguee aux sous-agents ([model-delegation.md](model-delegation.md)) ; les gros grains personnels seulement une fois les lanes servies et les merges prets epuises.

Detail complet (workflow batch merge + commandes + audit pre-merge + incidents + verbatims + mapping lanes + listes de rollout + 4-mecanismes de chaque regle) : [docs/secrets-and-coord-detail.md §2](../../docs/reference/secrets-and-coord-detail.md#2-coordinator-discipline-ai-01).

## Regle 0 : production avant digestion, sans perte de qualite (HARD)

La production des lanes et la digestion (CI, reviews, merges) sont **deux pipelines paralleles**. Une saturation du second est un symptome a reparer ou a capaciter ; elle ne devient jamais une politique de ralentissement du premier.

- Un check rouge, un `DWELL`, une review en attente, un conflit ou un HOLD bloque **la candidate concernee**, jamais la lane. La lane traite ce qu'elle peut reparer, puis poursuit aussitot un nouveau grain DEEP/MED de contenu pendant toute attente externe.
- `candidate-delivered`, forensic sans finding, body-only, attente mecanique, `HORS CAP` et backlog de review ne satisfont ni le plancher de production ni une fin de cycle.
- Quand le debit de digestion baisse, ai-01 maintient les deep queues et ouvre **en parallele** la piste de remise en capacite : diagnostic CI, sweep de merge supplementaire, ou correction de l'organe bloque. Il ne reduit pas les dispatchs pour rendre la queue confortable.
- ai-01 delegue agressivement la preparation verifiable : l'adjoint absorbe en file continue des lots oldest-first de preflights B.0/exact-head, relectures post-fix et recalculs ; Hermes et NanoClaw absorbent la premiere digestion specialisee. Chaque lot inventorie toutes les reserves de chaque candidate et remonte chaque READY sans attendre la fin du lot. Ces avis preparent la decision sans remplacer la lecture B.0 personnelle finale, les controles qualite ni la signature de merge d'ai-01.
- **Aucun de mes messages n'est un prealable (HARD, mandat user 2026-09-12).** Je n'ecris jamais une phrase dont l'effet est de suspendre une lane — « attends », « ne touche pas », « n'investigue pas avant que », « tiens ca jusqu'a » — sans nommer **dans la meme phrase** ce que la lane fait a la place. Une reserve, un HOLD ou un gate que je pose s'attache a la candidate et **me** revient a executer quand il exige une capacite que la lane n'a pas (#15463) ; il ne se delegue jamais en attente.
- **La profondeur de ma file de merge n'est jamais le champ de vision d'une lane.** Mesure du 2026-09-12 : **71 des 76 PRs ouvertes (93 %) n'attendaient aucun geste de lane** — 26 pretes a merger, 45 en attente de ma review. Une flotte dont la production est garee chez moi finit par prendre la surveillance de ma file pour du travail : c'est **mon** echec de digestion, et il se repare par des merges, jamais en steerant les lanes vers leur propre file.
- Une candidate prete n'attend pas le cron suivant : ai-01 refait la capture B.0/exact-head/gates et merge des qu'elle est sure. Les controles B.0, H.4 et G-VAR restent inchanges ; augmenter le debit ne signifie jamais les contourner.

## Regle 1 : ai-01 merge activement sous `myia-ai-01`

Le compte `myia-ai-01` **a** le droit `MergePullRequest` sur `jsboige/CoursIA` (verifie firsthand 2026-08-08 : 6 merges consecutifs sans aucun `gh auth switch`). Le `404` sur la protection de branche (#9991) dit que `jsboige` est requis pour **lire/modifier cette protection**, PAS pour merger — ne pas confondre.

Quand 1+ PR(s) CLEAN MERGEABLE + APPROVED s'accumulent : merger directement sous `myia-ai-01` (`gh pr merge <N> --squash`), puis post dashboard ack. **Pas** de "pending user merge" dans le todo. Reserver `gh auth switch -u jsboige` aux operations qui l'exigent : protection de branche, et PRs etudiantes ([student-pr-reviews.md](student-pr-reviews.md)) — le switch mute un etat **global au process `gh`** qui entre en course avec toute autre session appelant `gh` ([model-delegation.md](model-delegation.md) regle 6), donc le prescrire inutilement est un risque net.

**JAMAIS `--delete-branch`** au merge (incident #10093) : la branche est ce qui permet de rouvrir une PR fermee par erreur — #10067 n'a survecu a une fermeture involontaire que parce que sa branche etait intacte.

**Exception** : PR notebook -> regle H.4 (`git checkout` + Papermill local + verify `execution_count`) AVANT merge.

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
2. **Grounder chaque grain firsthand AVANT de dispatcher** (`gh issue view N` / `gh pr view N`), jamais depuis le status condense. Un steer qui pointe une issue CLOSED / une PR mergee / un rollout sature = phantom. Worker firsthand-sature → **le croire**, fournir un grain HORS scope. **Un body d'issue est date de sa redaction, pas de sa lecture** : `gh issue view N` est un status condense de plus des qu'un merge est passe apres. Grounder = lire l'**artefact** (`git log -- <fichier>` + le fichier sur `main` courant) **et** le **plateau** (`gh pr list` sur le chemin), pas le body seul.
3. **DECIDER les design-gates, ne pas deferer** : greenlight nomme + acceptance dans le cycle. Deferer une option deja investiguee = fabriquer de l'idle.
4. **Familles matures = fallback perenne epuisable** → deux sources never-empty le remplacent : **(a) CREATION SUBSTANTIELLE** scopee-coordinateur (nouveaux lakes Lean, audits axe-2 SOTA, consolidation, notebooks) stockee en avance ; **(b) DIVERSITE DU BACKLOG en souffrance** — piocher **une tranche concrete** par cycle de vieilles issues/EPICs, varier genres ET familles, jamais tunneliser un mono-theme.

**Tell d'auto-detection** avant de poster un steer : « (a) grain verifie OPEN/non-sature firsthand a l'instant, **et aucune PR ouverte sur ce chemin** ? (b) la decision atteint-elle l'inbox du worker ? (c) ai-je tranche, ou defere ? » — trois oui requis, sinon phantom. Le (a) se pose **avant** de rediger, pas apres (cf L898, [proactive-coordination.md](proactive-coordination.md)).

Mandat 2026-06-26 (verbatim) + listes d'issues des sources (a)/(b) : [§2.5](../../docs/reference/secrets-and-coord-detail.md#2-coordinator-discipline-ai-01). Voir aussi [[verify-before-claiming]], [[diversity-backlog-aged-issues]], [[feedback-double-dm-with-dashboard-notif]].

## Regle 6 : l'adjoint — verification delegable, jamais merge ni fermeture (HARD)

**Lane de l'adjoint : `myia-po-2025:CoursIA-2`** (preflight #13605 `issuecomment-5467391147`, cas `ADJOINT PREFLIGHT` de `check_unaddressed_nits.py` PR #13883, recalculs firsthand DM `msg-20260904T043716-lo9ryu`).

Mandat user 2026-09-07 (verbatim, #15069) : « si ton travail de coordination est sature, c'est tout a fait un travail de **verification** que tu peux deleguer a ton adjoint, mais **pas a nos plus petits workers** ».

| Routable a l'adjoint | JAMAIS (reste au coordinateur) |
|---|---|
| Verification pre-fermeture de l'urne `delivered` (preuve firsthand, G.9) | La fermeture elle-meme (`gh issue close`) |
| Preflight de PR (lecture body/comments/reviews + verdict `[adjoint — preflight COMMENTED]`) | Le merge (`gh auth switch` + merge reste ai-01) |
| Recalcul firsthand d'un verdict ou d'une metrique contestee | Toute decision de perimetre/design-gate |

L'adjoint **est** la lane habilitee n°3 de `DELIVERED_URN_LANES` dans `pick_idle_grain.py` (#15069) : il tire l'urne `delivered`, verifie, poste sa preuve — et la fermeture effective reste signee coordinateur. Une lane worker qui rencontre une `candidate-delivered` poste `[INFO] candidate-delivered` avec sa preuve et rend la main (cf [proactive-coordination.md](proactive-coordination.md), urne `delivered`).

## Voir aussi

- [proactive-coordination.md](proactive-coordination.md) — 1 PR/wakeup plancher, backlog pickup 8 sources, queue profonde
- [git-workflow.md](git-workflow.md) — branches feature/, no force push
- [pr-review-discipline.md](pr-review-discipline.md) — Critere CHANGES_REQUESTED
- CLAUDE.md section A — ai-01 review et merge, agents ne mergent pas
- CLAUDE.md section H.4 — Merges coord JAMAIS complaisants
