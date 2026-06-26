# Coordinator discipline — merge actively, no languishing requests

S'applique au **coordinateur ai-01** (`myia-ai-01:CoursIA`).

## Regle 1 : ai-01 merge soi-meme via `gh auth switch`

Le compte `myia-ai-01` n'a **pas** le droit `MergePullRequest` (GraphQL) sur `jsboige/CoursIA`. Le compte `jsboige` (token avec scopes `repo workflow`) a les droits.

Quand 1+ PR(s) CLEAN MERGEABLE + APPROVED s'accumulent : `gh auth switch -u jsboige` → merge → `gh auth switch -u myia-ai-01` → post dashboard ack. **Pas** de "pending user merge" dans le todo. Ne pas confondre "permissions GitHub absent" avec "interdiction de merger".

**Exception** : PR notebook → regle H.4 (`git checkout` + Papermill local + verify `execution_count`) AVANT merge.

User feedback explicite 2026-05-19 : "Fais un switch pour merger toi meme stp".

## Regle 2 : aucune demande user ne pourrit > 1 cycle

Quand le user formule une demande concrete et realisable :
- **< 30 min, action locale** : executer dans la session courante. Pas "on verra prochain cycle".
- **30 min - quelques heures** : creer immediatement dispatch + post dashboard `[INFO]` + acker user au tour suivant.
- **Multi-day** : creer immediatement GitHub issue avec scope + acceptance + label + ack user.

**Anti-patterns interdits** :
- "Je note pour prochain cycle" sans tracking concret (issue/dispatch/dashboard line)
- Recycler la demande a travers plusieurs `MEMORY.md` updates sans action
- Attendre que user re-formule pour agir

**Verification fin de session** : avant `[DONE]` dashboard, parcourir les N derniers messages user et confirmer que chaque demande a soit (a) ete executee, (b) eu un dispatch concret trace, (c) eu une issue ouverte, (d) ete explicitement reportee avec justification ecrite acceptee par user.

Bonus G.9 : "qu'est-ce que le user a demande que je n'ai pas encore fait ?" est un meilleur reflexe que "qu'est-ce qui reste a faire dans mon plan ?".

Workflow batch merge complet (commandes + audit pre-merge) + triage detail + incident origine : [docs/secrets-and-coord-detail.md](../../docs/reference/secrets-and-coord-detail.md#2-coordinator-discipline-ai-01).

## Regle 3 : coordonner CHAQUE lane (dashboard) independamment

Il existe **deux dashboards workspace** : `workspace-CoursIA` et `workspace-CoursIA-2`. **Aucun n'est "le dashboard du coordinateur"** — ce sont deux lanes co-egales. Un `lane` = **machine x workspace** : chaque machine worker qui a une lane CoursIA-2 a **AUSSI** une lane CoursIA (po-2026:CoursIA Lean / po-2026:CoursIA-2 Grothendieck ; po-2024:CoursIA QC / po-2024:CoursIA-2 MGS-.NET ; po-2025:CoursIA Python-ML / po-2025:CoursIA-2 .NET-Argumentum).

Chaque cycle `/coordinate`, ai-01 doit **LIRE *et* POSTER une coordination lane-specific sur LES DEUX**, independamment :
- **Lire** `section:"all"` des deux dashboards (pas un seul) — sinon les ASKs/blockers d'une lane restent invisibles.
- **Poster** un contenu **propre a chaque lane** (ses ASKs, ses merges, ses dispositions) — **jamais de broadcast miroir** (copier-coller identique des deux cotes).
- **Anti-pattern interdit** : traiter `workspace-CoursIA` comme « le mien » et `workspace-CoursIA-2` comme « celui des workers ». Les deux portent du travail worker a coordonner.
- **Piege duplication cross-lane** : un worker peut dedoubler une livraison sur ses deux lanes (ex #2950 sur CoursIA + #2952 sur CoursIA-2 pour le meme #1027). Reconcilier explicitement : 1 canonique mergee, l'autre disposee.

Source : mandat user 2026-06-14. Incident : un cycle entier ou seule la lane CoursIA-2 a ete coordonnee (broadcast miroir), ratant l'ASK greenlight PR1.5 Knot #2874 de po-2026:CoursIA et le rapport C.2 de #2953 (po-2025:CoursIA).

## Regle 4 : JAMAIS sanctionner une lane idle — deep-queue + fallback perenne (HARD)

S'applique meme quand ai-01 est **mobilise par le user** sur une autre tache (session interactive longue) : c'est precisement le cas que les deux mecanismes doivent couvrir. Source : incident 2026-06-16 — pendant une session Sudoku-13 longue, j'ai poste « po-2026 honest-idle legit / po-2024 await dispatch / po-2025 nearing exhausted ». Les workers ont **cite ma sanction** comme licence pour stand-down. Le user (verbatim) : « tu n'as pas prevu de deep queue comme on a dit, ni d'idle lane pour qu'il n'y ait jamais rien a faire ».

1. **Interdit de sanctionner l'idle.** ai-01 ne poste **JAMAIS** un statut de lane terminal-idle : « honest-idle legit », « lane exhausted/closed », « await dispatch » **comme etat final**. Une lane idle = **echec ai-01**, pas un etat acceptable du worker (cf [[never-close-a-lane-feed-deep-queue]]). Si je n'ai pas de dispatch frais, je donne la **queue profonde + le fallback perenne** ci-dessous — jamais « rien a faire ».

2. **Deep queue = ~5-10 steps ordonnes par lane, sur le dashboard.** Assez profonde pour couvrir **plusieurs cycles de coord meme si ai-01 est absent/mobilise plusieurs heures**. Pre-autorisation explicite dans le post : « brule-les **dans l'ordre**, NE m'attends PAS entre steps, ASK seulement sur **blocker reel** ou **queue vide** » (cf [[feedback-dispatch-fill-spare-capacity]]).

3. **Fallback perenne never-empty par famille = le filet qui ne tombe jamais a sec.** Quand la deep-queue Epic d'une lane est genuinement epuisee, le worker **NE rapporte PAS idle** : il tombe sur le fallback perenne de SA famille, qui ne se vide jamais :
   **Un tracker FERME ne ferme pas le rollout** : le travail repo-wide famille-partitionne persiste meme quand l'issue-Epic de suivi est CLOSED — ne JAMAIS lire « issue closed » comme « fallback indisponible » (incident recurrent 2026-06-25 : 3 lanes ont rapporte idle en citant #2651/#2161 CLOSED, alors que la prose et les 3-exercices restent a faire notebook par notebook). Rollouts perennes LIVE (OPEN au 2026-06-25, famille-partitionnes) :
   - **#3973 feuilles-READMEs ascendantes** (filles par famille : #3974 GenAI+Python, #3975 SymbolicAI-non-Lean+Sudoku+GameTheory+CaseStudies, #3976 QuantConnect, #3978 SymbolicAI/Lean, #3979 Knot/Grothendieck). **Successeur LIVE de #2651** (prose pedagogique, CLOSED).
   - **#4212 finition editoriale** (aeration prose + visuels Mermaid/GenAI, rolling famille-partitionne, Part of #4208).
   - **#3870 backfill FR des READMEs EN** (#1650 Phase 0.5, ~15 READMEs, preserve `README.en.md`).
   - **#2876 accents manquants** dans les READMEs francophones (good first issue, repo-wide).
   - **Convention 3 exercices/notebook** (`.claude/rules/three-exercises-per-notebook.md`, rule ongoing — tracker #2161 CLOSED mais rollout a faire notebook par notebook).
   Ces rollouts sont repo-wide et famille-partitionnes → une lane n'est **jamais** vide. `[CLAIMED] <item> — <machine:workspace> <ts>` avant de commencer (anti-double-claim). **Quand un tracker LIVE ci-dessus est ferme a son tour, ai-01 le remplace par son successeur OPEN — ce point ne pointe JAMAIS vers une issue CLOSED.**

4. **Token economy ne ferme jamais une lane Lean/research.** L'economie de tokens est **Anthropic-only** (cf [[feedback-token-economy-anthropic-only]]) ; sur les workers z.ai/GLM (large) elle n'est PAS une contrainte. Un worker qui HOLD du Lean/proving en citant « token economy z.ai » se trompe — decomposer les sorries jusqu'au noyau dur irreductible (1-2 genuinement intractables OK a laisser, documentes). ai-01 ne valide pas un HOLD Lean motive par l'economie.

## Regle 5 : le STEER doit ATTEINDRE le worker, etre VRAI, et DECIDER — pas un post dashboard phantom (HARD)

Source : mandat user 2026-06-26 (« je ne veux PLUS JAMAIS trouver de workers oisifs ... tes dispatchs longue queue ne tiennent pas, tes taches idle ne tiennent pas, ou ta facon de coordonner n'est pas la bonne »). Diagnostic firsthand (wakeup po-2024:CoursIA-2 montre par le user) : un worker mature firsthand-sature, qui refuse correctement de fabriquer du filler (G.9 + anti-filler), reste oisif quand le coordinateur (a) poste ses steers sur l'intercom dashboard (qui **auto-condense/archive chaque cycle**), (b) les redige depuis le **status CONDENSE** (qui hallucine : confond un `[DONE]` avec un merge, pointe des issues CLOSED), et (c) **defere** les design-gates au lieu de trancher. Resultat = steers **phantom** (4 cycles de suite sur une meme lane), le worker brule ses cycles a les refuter au lieu de produire. **L'idle est un echec COORDINATEUR, jamais worker** (renforce Regle 4).

Les 4 mecanismes correctifs (chaque cycle, par lane) :

1. **Livrer la decision en DIRECT MESSAGE** (`roosync_messages send`/`reply` vers `machine:workspace`), **pas seulement** un append dashboard. Le tour du worker lit `inbox status:unread` EN PREMIER ; un message direct y atterrit et **survit a la condensation**. Un steer qui ne vit que dans l'intercom est archive avant le prochain wakeup = il « ne tient pas ». Le dashboard reste le backstop persistant, **pas** le canal de decision.

2. **Grounder chaque grain firsthand AVANT de dispatcher.** `gh issue view N` / `gh pr view N --json state,mergeStateStatus` sur CHAQUE issue/PR cite — **jamais** depuis le status condense. Un steer qui pointe une issue CLOSED, une PR deja mergee, ou un rollout deja sature = phantom (cf [[verify-before-claiming]], `stale-steer`). Si le worker a firsthand-rapporte une saturation, **le croire** et fournir un grain HORS de ce scope, pas re-pointer le scope sature.

3. **DECIDER les design-gates, ne pas deferer.** Quand un worker surface des options de design (ex : « greenlight (b)/(c)/(d) ? ») avec son investigation firsthand, **trancher dans le cycle** — un greenlight nomme + acceptance. Deferer = fabriquer de l'idle. « Je note pour le prochain sweep » sur une option deja investiguee = manquement.

4. **La premisse « fallback perenne jamais vide » FAILE pour les familles MATURES — deux sources la remplacent.** Les rollouts mecaniques famille-partitionnes (#2161 3-exos, #3973 feuilles-READMEs, #4212 Mermaid, #2876 accents, #3870 FR) **s'epuisent reellement** par famille — un worker peut etre genuinement 100% conforme sur toute sa partition (verifiable G.1). Quand c'est le cas, **ne pas re-pointer le fallback** (= phantom Regle 5.2). Les deux sources never-empty restantes :
   - **(a) CREATION SUBSTANTIELLE** scopee-coordinateur : nouveaux lakes Lean (#4038), audits axe-2 SOTA (#3801, self-verifying = livrable dans les deux issues), consolidation lakes (#4362), nouveaux notebooks. ai-01 maintient cette queue **stockee en avance** sur le rythme de consommation.
   - **(b) DIVERSITE DU BACKLOG EN SOUFFRANCE** (mandat user 2026-06-26) : le depot porte **des dizaines d'issues anciennes/priority-low/EPICs partiellement avancees** qui meritent d'etre **avancees au compte-goutte** — #16 (securisation services IA, 03-03), #417 (OWUI tests+docs), #569 (QC-masterclass Jared), #1206 (Z3.Linq fork), #1210 (semantic-fleet debt), #2137 (Argumentum), #3436 (papermill-paths repo-wide)… **Piocher une tranche concrete par cycle** (pas l'EPIC entier d'un coup), **varier genres ET familles** cycle apres cycle, ne JAMAIS tunneliser un mono-theme. Une vieille issue figee depuis des semaines merite **une tranche**, pas l'oubli. Grounder firsthand (Regle 5.2) avant de dispatcher : beaucoup de vieux EPICs ont des tranches deja faites.

   C'est plus de scoping coordinateur — c'est le cout reel de la maturite du depot, pas une option.

**Tell d'auto-detection** : avant de poster un steer, se demander « (a) ce grain est-il verifie OPEN/non-sature firsthand a l'instant ? (b) la decision atteint-elle l'inbox du worker ? (c) ai-je tranche, ou defere ? ». Trois oui requis. Sinon = phantom, le worker idlera.

## Voir aussi

- [.claude/rules/proactive-coordination.md](proactive-coordination.md) — 1 PR/wakeup plancher, backlog pickup 8 sources, queue profonde
- [.claude/rules/git-workflow.md](git-workflow.md) — branches feature/, no force push
- [.claude/rules/pr-review-discipline.md](pr-review-discipline.md) — Critere CHANGES_REQUESTED
- CLAUDE.md section A — ai-01 review et merge, agents ne mergent pas
- CLAUDE.md section H.4 — Merges coord JAMAIS complaisants
