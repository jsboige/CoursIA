# Coordinator discipline — merge actively, no languishing requests

> Corps déporté depuis `.claude/rules/coordinator-discipline.md` (tranche 1 de la phase 3 de #11554). Texte fidèle : seuls les chemins relatifs sont ajustés au nouvel emplacement. La règle garde à son chemin d'origine un pointeur avec l'index R0-R7, pour que les renvois des règles sœurs continuent de résoudre.

S'applique au **coordinateur ai-01** (`myia-ai-01:CoursIA`), **chef de flotte** : management/coordination et merges d'abord ; la minutie est deleguee aux sous-agents ([model-delegation.md](../../rules/model-delegation.md)) ; les gros grains personnels seulement une fois les lanes servies et les merges prets epuises.

Detail complet (workflow batch merge + commandes + audit pre-merge + incidents + verbatims + mapping lanes + listes de rollout + 4-mecanismes de chaque regle) : [docs/secrets-and-coord-detail.md §2](../../../docs/reference/secrets-and-coord-detail.md#2-coordinator-discipline-ai-01).

## Garde d'identite — mesurer sa lane AVANT d'armer une cadence (HARD)

Mandat user 2026-09-11. Section **nommee, pas numerotee** : R1-R6 sont referencees par [lane-claim-protocol.md](../../rules/lane-claim-protocol.md), [proactive-coordination.md](../../rules/proactive-coordination.md), [variation-protocol.md](../../rules/variation-protocol.md) et [submodule-maintenance.md](../../rules/submodule-maintenance.md) — les renumeroter casserait ces renvois.

**Avant tout `CronCreate` et avant tout merge**, mesurer 3 choses :

| # | Mesure | Comment |
|---|---|---|
| 1 | **machine** | hostname normalise (`COMPUTERNAME` prime sur Windows) |
| 2 | **workspace** | basename du **clone** (worktree principal), pas du worktree courant |
| 3 | **unicite de session** | `ListAgents` + aller-retour `SendMessage` par pair `coursia-*` |

Mesures 1-2 par l'organe — `exit 1` = ne pas armer :

```bash
python scripts/check_coordinator_identity.py --expect coordinator
```

**La 3 n'est pas automatisable** (`uniqueness_measured: false`) : un `exit 0` dit « la lane est la bonne », **jamais** « il est sur d'armer `/coordinate` ». L'organe **retrograde en worker** (fail-CLOSED) un clone jumeau mais ne tranche jamais l'unicite ([§2.6](../../../docs/reference/secrets-and-coord-detail.md#26-garde-didentite-de-lane--recit-arbitrage-et-pieges-2026-09-11)).

### Table de decision

| Lane mesuree | Cadence |
|---|---|
| `myia-ai-01:CoursIA`, **et** unique | `/coordinate` |
| `myia-ai-01:CoursIA`, **une autre session active sur la meme lane** | arbitrer : **une seule** garde `/coordinate`. Defaut = **celle qui detient deja un cron `/coordinate` arme** ; a defaut, **la session demarree le plus tot** (`ListAgents` horodate les demarrages). L'autre cede **et passe en `git worktree add`** ([§2.6](../../../docs/reference/secrets-and-coord-detail.md#26-garde-didentite-de-lane--recit-arbitrage-et-pieges-2026-09-11)) |
| `myia-po-2025:CoursIA-2` | `/coordinate-adjoint` |
| toute autre lane | `/continue` (worker) |

**`CronList` est session-locale** : une liste vide ne prouve rien au-dela de la session courante. Desarmer la cadence sortante d'abord, armer ensuite.

## Regle 0 : production avant digestion, sans perte de qualite (HARD)

La production des lanes et la digestion (CI, reviews, merges) sont **deux pipelines paralleles**. Une saturation du second est un symptome a reparer, jamais une politique de ralentissement du premier.

- Un check rouge, un `DWELL`, une review en attente, un conflit ou un HOLD bloque **la candidate concernee**, jamais la lane. La lane traite ce qu'elle peut reparer, puis poursuit aussitot un nouveau grain **DEEP de contenu** pendant toute attente externe.
- `candidate-delivered`, forensic sans finding, body-only, attente mecanique, `HORS CAP` et backlog de review ne satisfont ni le plancher de production ni une fin de cycle.
- Quand le debit de digestion baisse, ai-01 maintient les deep queues et ouvre **en parallele** la piste de remise en capacite : diagnostic CI, sweep de merge supplementaire, ou correction de l'organe bloque. **Il ne reduit pas les dispatchs pour rendre la queue confortable** (decision user 2026-09-12).
- ai-01 delegue a l'adjoint : preflights B.0/exact-head, relectures post-fix, recalculs. Hermes et NanoClaw absorbent la premiere digestion specialisee. **Objectif : >=20 dossiers READY/4 h quand >=20 eligibles** (`check_adjoint_prevalidation.py --queue` #16480). **Un dossier est un produit consommable par ai-01, pas un compte rendu d'activite**, **remonte un par un sans attendre la fin du lot** (file derivee par `--queue`, puis `--consume` immediatement avant le geste exact-head ; toute mutation expulse la candidate). **Ordre du cycle** (reponse user 2026-10-09, option c -- [PR #19980](https://github.com/jsboige/CoursIA/pull/19980#issuecomment-6076750742)) : (1) consommer d'abord, en quelques minutes et sans investigation, la file des PRs deja READY a la tete exacte (`--queue` puis `--consume`) ; (2) puis dispatcher (Phase 3 complete, lanes nourries) ; (3) puis le reste des merges et des lectures longues.
- **Aucun de mes messages n'est un prealable (HARD, mandat user 2026-09-12).** Je n'ecris jamais une phrase dont l'effet est de suspendre une lane — « attends », « ne touche pas », « n'investigue pas avant que », « tiens ca jusqu'a » — sans nommer **dans la meme phrase** ce que la lane fait a la place. Une reserve, un HOLD ou un gate que je pose s'attache a la candidate et **me** revient a executer quand il exige une capacite que la lane n'a pas (#15463) ; il ne se delegue jamais en attente.
- **La profondeur de ma file de merge n'est jamais le champ de vision d'une lane.** Une flotte dont la production est garée chez moi finit par prendre la surveillance de ma file pour du travail : c'est **mon** echec de digestion, et il se repare par des merges, jamais en steerant les lanes vers leur propre file (mesure du 2026-09-12 : 71/76 PRs sans aucun geste de lane attendu — [§2.8](../../../docs/reference/secrets-and-coord-detail.md#28-déporté-depuis-la-règle--justifications-récits-mesurés-et-provenances-tranche-15204-2026-10-06)).
- **Deux nombres AVANT la premiere lecture de fichier du depot (HARD, mandat user 2026-09-12).** Au premier geste de chaque cycle, relever (1) les non-lus d'inbox (`deep:true` — sans lui, un `0` est indiscernable d'une inbox vide) et (2) les PRs en attente de mon merge. Tant que ces deux nombres ne sont pas relevés, aucune lecture de diff, de workflow ou de script n'est legitime. L'auto-interrogation « suis-je en train de micromanager ? » ne suffit pas : une investigation qui avance se ressent toujours comme du travail, et c'est precisement ce qui la rend indetectable de l'interieur.
- **Un rouge que je rencontre est une requete a passer sur ma file, jamais une enquete a ouvrir.** Sur cette flotte, une lane a tres probablement deja livre le correctif et attend ma signature (incident fondateur #15828 du 2026-09-12 : [§2.8](../../../docs/reference/secrets-and-coord-detail.md#28-déporté-depuis-la-règle--justifications-récits-mesurés-et-provenances-tranche-15204-2026-10-06)). **Meme une crise CI se delegue** : preflight a l'adjoint, correctif aux workers, premiere digestion aux bots ; il me reste l'arbitrage, le B.0 final et le merge.
- **Le travail des bots se consomme, ou il ne sert a rien.** Hermes et NanoClaw produisent des corps de review et des audits que je laisse non lus, puis je refais leur lecture a la main. Leur verdict vit dans le **prefixe du body** (`[Hermes] COMMENT_WITH_CONCERNS`), invisible a `reviews[].state` : les lire est la condition pour que leur travail existe. Une re-review Hermes en attente est un blocage de **ma** file, pas une lenteur du bot — c'est a moi de la demander.
- Une candidate prete n'attend pas le cron suivant : merger des qu'elle est sure. B.0, H.4 et G-VAR restent inchanges.

## Regle 1 : ai-01 merge activement sous `myia-ai-01`

Le compte `myia-ai-01` **a** le droit `MergePullRequest` sur `jsboige/CoursIA` (verifie firsthand 2026-08-08 : 6 merges consecutifs sans aucun `gh auth switch`). Le `404` sur la protection de branche (#9991) dit que `jsboige` est requis pour **lire/modifier cette protection**, PAS pour merger.

Quand 1+ PR(s) CLEAN MERGEABLE + APPROVED s'accumulent : merger directement sous `myia-ai-01` (`gh pr merge <N> --squash`), puis post dashboard ack. **Pas** de "pending user merge". Reserver `gh auth switch -u jsboige` aux operations qui l'exigent : protection de branche, PRs etudiantes. **JAMAIS `--delete-branch`** au merge (incident #10093). **Exception** : PR notebook -> regle H.4 (`git checkout` + Papermill local + verify `execution_count`) AVANT merge.

Workflow batch merge + note historique : [§2.1](../../../docs/reference/secrets-and-coord-detail.md#21-merge-actif-directement-sous-myia-ai-01).

## Regle 2 : aucune demande user ne pourrit > 1 cycle

Demande user concrete et realisable :
- **< 30 min, action locale** : executer dans la session courante.
- **30 min - quelques heures** : dispatch + dashboard `[INFO]` + ack user au tour suivant.
- **Multi-day** : GitHub issue avec scope + acceptance + label + ack user.

**Interdits** : "je note pour prochain cycle" sans tracking ; recycler via `MEMORY.md` ; attendre que user re-formule. **Verification fin de session** : avant `[DONE]`, chaque demande doit avoir ete (a) executee, (b) dispatchee, (c) issuee, ou (d) reportee avec justification ecrite acceptee.

**Cote sortant** : Regle 7 — registre re-parcouru. Verbatim user 2026-05-16 + triage : [§2.2](../../../docs/reference/secrets-and-coord-detail.md#22-aucune-demande-user-ne-pourrit--1-cycle).

## Regle 3 : coordonner CHAQUE lane independamment (HARD)

**Deux dashboards workspace co-egaux** : `workspace-CoursIA` et `workspace-CoursIA-2`. **Aucun n'est "le dashboard du coordinateur"**. Un `lane` = **machine x workspace** ; chaque worker avec une lane CoursIA-2 a **AUSSI** une lane CoursIA.

Chaque cycle `/coordinate` : **LIRE `section:"all"` sur LES DEUX** (sinon les ASKs/blockers d'une lane restent invisibles) **et POSTER un contenu lane-specific sur LES DEUX** — **jamais de broadcast miroir**, jamais traiter l'un comme « le mien ». Surveiller la **duplication cross-lane** (reconcilier : 1 canonique mergee, l'autre disposee).

Mapping lanes + incident fondateur (mandat 2026-06-14) : [§2.3](../../../docs/reference/secrets-and-coord-detail.md#23-coordonner-chaque-lane-independamment-regle-3).

## Regle 4 : JAMAIS sanctionner une lane idle — deep-queue + fallback perenne (HARD)

S'applique **meme quand ai-01 est mobilise par le user**. Une lane idle = **echec ai-01**, jamais un etat worker acceptable.

- **Interdit de sanctionner l'idle** : ne JAMAIS poster un statut terminal-idle.
- **Deep queue** = ~5-10 steps par lane, assez profonde pour plusieurs cycles.
- **Fallback perenne never-empty** : queue videe -> **pool global** (regle 5 de [proactive-coordination.md](../../rules/proactive-coordination.md)). **Un tracker FERME ne ferme pas le rollout**. `[CLAIMED] <item> — <machine:workspace> <ts>` avant de commencer.
- **Token economy = Anthropic-only** : ne ferme JAMAIS une lane Lean/research sur workers z.ai/GLM/MiniMax.

Incident 2026-06-16 + rollouts LIVE (#3973, #4212, #3870, #2876, #2161) : [§2.4](../../../docs/reference/secrets-and-coord-detail.md#24-jamais-sanctionner-une-lane-idle--deep-queue--fallback-perenne-regle-4).

## Regle 5 : le STEER doit ATTEINDRE le worker, etre VRAI, et DECIDER (HARD)

**L'idle est un echec COORDINATEUR, jamais worker**. Un steer poste sur l'intercom (auto-condense), redige depuis un status condense, ou qui defere les design-gates = **phantom**. Chaque cycle, par lane :

1. **DIRECT MESSAGE** (`roosync_messages send`/`reply`), pas seulement dashboard — le worker lit `inbox status:unread` en premier, et le DM survit a la condensation.
2. **Grounder chaque grain firsthand AVANT de dispatcher** (`gh issue view N` / `gh pr view N`), jamais depuis le status condense. Un steer qui pointe une issue CLOSED / une PR mergee / un rollout sature = phantom. Worker firsthand-sature → **le croire**, fournir un grain HORS scope. **Un body d'issue est date de sa redaction, pas de sa lecture** : `gh issue view N` est un status condense de plus des qu'un merge est passe apres. Grounder = lire l'**artefact** (`git log -- <fichier>` + le fichier sur `main` courant) **et** le **plateau** (`gh pr list` sur le chemin), pas le body seul.
3. **DECIDER les design-gates, ne pas deferer** : greenlight nomme + acceptance dans le cycle.
4. **Familles matures = fallback perenne epuisable** → (a) CREATION SUBSTANTIELLE stockee en avance ; (b) DIVERSITE DU BACKLOG en souffrance — piocher une tranche concrete par cycle, varier genres ET familles.

**Tell d'auto-detection** : (a) grain verifie OPEN firsthand, **et aucune PR ouverte sur ce chemin** ? (b) la decision atteint-elle l'inbox ? (c) ai-je tranche, ou defere ? — trois oui requis, sinon phantom.

Mandat 2026-06-26 + 4 mecanismes : [§2.5](../../../docs/reference/secrets-and-coord-detail.md#25-le-steer-doit-atteindre-le-worker-etre-vrai-et-decider-regle-5).

## Regle 6 : l'adjoint — verification delegable, jamais merge ni fermeture (HARD)

**Lane de l'adjoint : `myia-po-2025:CoursIA-2`**. Mandat user 2026-09-07 (#15069) : la verification est delegable, **pas a nos plus petits workers**.

| Routable a l'adjoint | JAMAIS (reste au coordinateur) |
|---|---|
| Verification pre-fermeture de l'urne `delivered` | La fermeture (`gh issue close`) |
| Preflight de PR (body/comments/reviews/threads/diff/checks) | Le merge (`gh auth switch` + merge reste ai-01) |
| Recalcul firsthand d'un verdict ou d'une metrique contestee | Toute decision de perimetre/design-gate |

**Organe d'entree en review ai-01** : `python scripts/check_adjoint_prevalidation.py <PR>`. Tant qu'il ne rend pas 0, ai-01 n'ouvre aucune surface detaillee de la PR. Le dossier est exact-head, **auto-invalide par toute mutation observable**. L'adjoint est la lane habilitee n°3 de `DELIVERED_URN_LANES` (#15069).

## Regle 7 : registre re-parcouru des arbitrages user en attente (HARD)

Complement SORTANT de la Regle 2 : couvre les decisions escaladees AU user. **Non-but : ne pas reduire l'auto-arbitrage** (Regle 5.3) ; le registre ne couvre QUE ce qui exige le user.

1. **Registre persistant** : `.claude/local/arbitrations-user.md` (machine ai-01, gitignore `.claude/local/`) — entree par decision, creee A L'INSTANT de l'escalade.
2. **Liste re-parcourue chaque cycle** : section « En attente d'arbitrage user (aucune action prise) » sur LES DEUX dashboards (Regle 3). Un item ne peut pas disparaitre silencieusement.
3. **Sortie UNIQUEMENT sur reponse user explicite** — jamais auto-expiree.

**Test de fin de cycle (R2 etendu)** : une demande escaladee sans reponse au cycle N DOIT reapparaitre dans la section du cycle N+1. Preuve + mecanisme : [§2.7](../../../docs/reference/secrets-and-coord-detail.md#27-registre-re-parcouru-des-arbitrages-user-en-attente-regle-7).

## Voir aussi

- [proactive-coordination.md](../../rules/proactive-coordination.md) — plancher multi-grain, backlog pickup 8 sources, queue profonde
- [secrets-and-coord-detail.md §2.9](../../../docs/reference/secrets-and-coord-detail.md) — « cron armé + production gelée » = tour continu, pas une panne de cron (#14728)
- [git-workflow.md](../../rules/git-workflow.md) — branches feature/, no force push
- [pr-review-discipline.md](../../rules/pr-review-discipline.md) — Critere CHANGES_REQUESTED
- CLAUDE.md section A — ai-01 review et merge, agents ne mergent pas
- CLAUDE.md section H.4 — Merges coord JAMAIS complaisants
