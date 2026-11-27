# Continue - Cycle worker

Reprendre le travail sur cette lane : lire les directives coordinateur, puis enchainer les reparations et grains substantiels tant que la session est active. C'est le prompt du cron worker (30 min staggered). **Un worker ne lance JAMAIS `/coordinate`** (lecon #1502) : pas de merge, pas de close d'issue d'autrui. **`gh auth switch` est autorise et necessaire** (trousseau gh partage entre workspaces — mandat user 2026-08-31) : la ligne rouge est le merge/close d'autrui, pas le switch lui-meme.

## Du verdict au prochain geste

Une réponse courte suffit si elle dit ce qui a changé sur le livrable. Une candidature écartée, un claim ou un message envoyé ne sont pas une livraison.
Si le grain dépend désormais d’un tiers, lui transmettre la pièce précise et la condition de reprise ; avancer la prochaine correction ou feuille attribuée sans rouvrir tout le catalogue. Les contrôles de claim et de validation restent inchangés.

## Workflow

### Phase 1 : Contexte (30s)

1. Etablir si la session précédente a été interrompue pour une raison fortuite (crash de l'environnement, saturation du crédit de tokens etc.), et quelles étapes restent à finaliser avant d'entreprendre une nouvelle session propre.
2. `python scripts/coordination/session_hygiene.py --lane <machine:workspace>` — verrou de session + hygiène de l'arbre en debut de cycle (#26632). Un ROUGE **session-double** = **arret** : `CronList` puis `CronDelete` du cron double **dans la session qui le porte** (split-brain, cf CLAUDE.md global), aucune edition tant qu'il vit ; les autres ROUGES (main otage, organes divergents de origin/main) se traitent avant le tirage.
3. Lire `MEMORY.md` (auto-memory) pour l'etat des sessions precedentes
4. `git checkout main && git pull --ff-only` — repartir d'un main courant (les branches feature se rebasent frais, cf [catalog-pr-hygiene](../rules/catalog-pr-hygiene.md))
5. `git status` — si l'arbre partage est sale (WIP d'une autre session), travailler en **worktree isole** : `git worktree add ../CoursIA-<sujet> -b feature/<sujet> origin/main`. Ne jamais stasher/toucher le WIP d'autrui.

### Phase 1.5 : Tour RooSync (obligatoire, AVANT de travailler)

1. **Inbox DM en PREMIER** : `roosync_messages(action:"inbox", status:"unread")` — le DM est le canal de decision du coordinateur, il survit a la condensation du dashboard.
2. **Dashboard workspace** : `roosync_dashboard(action:"read", type:"workspace", section:"all")` — chercher les `[DISPATCH→inbox]` et les steers de MA lane (`machine:workspace`). Si la machine a une lane CoursIA-2, lire aussi ce dashboard pour cette lane.
3. **Filtrage workspace** : traiter UNIQUEMENT les messages adresses a cette lane ou cette machine ; ignorer les autres workspaces.
4. Missions coordinateur (ai-01) HIGH/URGENT = priorite sur les taches locales. Accuser reception (reply DM ou dashboard).

### Phase 2 : Choisir la tache

**Avant le tirage : l'issue `[main-red]`.** Un rouge de `main` herite n'est plus un grain sans proprietaire : quand la sentinelle `main-red` de `merge_ready.py` retient les merges, elle ouvre (ou reutilise) UNE issue `[main-red] <check> — <test>`, que la lane qui repare reclame et que la sentinelle ferme au vert (#26706). La PR de reparation la **nomme** (`See #`), elle ne la ferme pas : la fermeture appartient a la sentinelle, qui la fait au vert mesure. A lire **avant** de reparer quoi que ce soit d'herite :

```bash
gh issue list --repo jsboige/CoursIA --state open --search "main-red in:title" --json number,title
```

- **Issue ouverte, claim d'une autre lane** → **ne pas ouvrir de travail dessus** : la cause est deja reprise. On attend son merge (verifie au cycle suivant) puis on `update-branch` sur nos branches. Ce n'est pas une attente bloquante : la file continue.
- **Issue ouverte, aucun claim** → c'est un grain de fond : on le reclame (`[CLAIMED] lane <machine:workspace> -- <cause>`) apres `python scripts/check_lane_claim.py <N>`, et la PR de reparation porte `See #<N>` — **pas** `Closes`. La fermeture appartient a la sentinelle : le correctif fusionne alors que `main` n'a pas encore rejoue `Scripts Tests (CPU)` (20 a 30 min), et une fermeture par la PR laisserait l'episode sans issue ouverte pendant ce temps.
- **Aucune issue** → le rouge n'est pas encore publie par la sentinelle (ou il est redevenu vert) : on suit la voie normale.

**Un seul geste ouvre le choix, une fois par session** (mandat user du 13/11 : plusieurs grains par session, grande variete, tirage court) :

```bash
python scripts/coordination/tapis_rapide.py --lane <machine:workspace>
```

Il rend **vos PRs ouvertes**, puis **8 grains de 8 familles differentes**, chacun avec la commande `check_lane_claim.py` a jouer avant d'editer ([tapis-rapide.md](../../docs/reference/tapis-rapide.md)). **La liste se sert en entier** ; on ne retire qu'une fois la liste epuisee. **Les grains passent avant les conteneurs** : un conteneur (EPIC, parapluie) vient en fin de liste, avec sa procedure (lire le fil entier, prendre l'etape suivante hors des chemins occupes qu'il imprime, verifier par `check_lane_claim.py N --lane <lane> --paths <vos chemins>`) ; sans `--paths`, l'organe refuse le conteneur entier des qu'une autre lane y tient un claim borne. Sortie 3 (lecture GitHub incomplete) : le tapis tire sur la derniere lecture complete de moins de 12 h du cache machine et le dit ; sans elle, rien n'est servi -- portez vos PRs, traitez votre file coordinateur, puis re-tirez. **Le tapis lourd `pick_idle_grain.py --belt` ne se tire plus** (240 s, grains non verifies, #26926). Sortie 4 (tirage REFUSE : la mesure n'a pas PU être faite — fetch raté ou référence illisible) : le remède est de rétablir l'accès à `origin/main` puis re-tirer, **JAMAIS le repli `pick_idle_grain`** — il se contente d'avertir et rejoue le même incident (po-2028, 14/11, #26632). Depuis I4 (#28114), un `main` local en retard ou un module du tirage divergent d'`origin/main` ne refusent **plus** le tirage : ils le **dégradent** (sortie 0, avertissement `TIRAGE DEGRADE [...]` sur stderr, verdict complet dans le rapport `fraicheur`) ; sous `ORGANE_DIVERGENT`, le code exécuté n'est **pas** identique à `origin/main` — remettre ces modules à leur version d'`origin/main` puis re-tirer.

**P0 — Reparer SON PROPRE rouge.** Les **nits** des PRs de la lane sont la **premiere file de la session**, avant tout grain neuf : repondre aux reserves, reparer un rouge propre a la PR, resoudre un conflit. Une PR verte, sans reserve ni conflit, qui n'attend que la review ou le merge du coordinateur **n'est pas du P0** : on ne la rafraichit pas, on ne la replie pas, on passe aux grains (mandat user du 17/11 : « Il devrait toujours être possible de produire, après le traitement prioritaire des nits »). La drainer ne termine pas la session. La raison est mecanique, pas disciplinaire : une PR rouge ne peut etre reparee **que par sa lane** — le coordinateur ne peut ni rebaser ni corriger a sa place — donc tant que la lane ne revient pas dessus, elle reste ouverte indefiniment pendant que les PRs du jour, elles, mergent. C'est exactement ce qui produit le residu de vieilles PRs.

- Une PR reparee **et mergee compte comme un grain du cycle** — jamais comme le plancher R1, qui exige un DEEP de CONTENU (un REPAIR est au mieux MED) : ce n'est pas un a-cote, c'est du travail deja ecrit qu'on porte a son terme.
- Rouge **non reparable par cette lane** (garde casse sur main, dependance d'une autre PR) : l'**ecrire en commentaire sur la PR**, avec le **numero de l'issue `[main-red]`** qui porte la cause (#26706), puis passer aux grains. L'echappatoire se justifie par ecrit, elle ne se prend pas en silence.
- Seule preemption : une mission coordinateur **URGENT** (le coordinateur voit le plateau entier).

**P1 — Missions coordinateur** : DM HIGH, puis steers dashboard de ma lane. **La file dispatchee a la lane est le tirage du tapis fait par le coordinateur** : a chaque tour, il tire les issues les moins visitees et compose pour chaque lane un arc coherent, a enchainer en multi-grain jusqu'au tour suivant. Elle se traite **en entier, dans son ordre**, avant tout tirage personnel ; le tapis (P3) complete la session quand la file est videe.

- **Rendre la main sur chaque issue de la file** : `[DELIVERED] lane <machine:workspace> -- PR #N -- paths: <fichiers de la PR>`, ou `[RELEASED] lane <machine:workspace> -- <motif>` quand une barriere reelle la fait sauter. Pour `[DELIVERED]`, relever les chemins dans `gh pr view N --json files` et les inscrire sur la ligne du marqueur ; employer des chemins exacts quand un glob deborderait le contenu livre. La clause borne l'occupation de l'issue aux seuls chemins livres tant que la PR est ouverte ou mergee. C'est ce marqueur, et non le claim pose au dispatch, qui la retire de l'assiette que le coordinateur mesure au tour suivant.
- **Tour de recette hebdomadaire** : `python scripts/coordination/recette_due.py --lane <machine:workspace>`. Sortie 1 (`DUE #N`) : servir cette issue en tete de file, en livrant au validateur humain une iteration qu'il peut examiner, ou en repondant a son dernier retour. Chaque lane le fait au moins une fois par semaine : chaque tour est un aller-retour de plus pour le validateur. Sortie 2 : organe injoignable, poursuivre sans.

**P2 — Travail en cours** : tache `[CLAIMED]` par cette lane non terminee.

**P3 — Le tapis** (sortie 0) : il tire dans **tout l'ouvert, cross-lane**. Les familles (racine d'EPIC) sont servies **a tour de role**, avec une **legere priorite** aux issues de consolidation et aux vieux Epics (mandat user du 13/11) ; dans une famille, l'issue la moins recemment visitee passe devant, et une issue jamais servie passe en tete. La lane est une etiquette de reporting, pas une frontiere de travail : rien n'est "le turf d'un autre". **Servir une issue, c'est d'abord la confronter a ses criteres** (body complet, amendements du fil, contre `main`) : tous couverts -> `[INFO] candidate-delivered` avec la preuve par critere, la cloture revient au coordinateur ou a l'adjoint ; un plan, une table ou une decision deja poste dans le fil -> le grain est **l'etape suivante de ce plan**, jamais un contenu neuf a cote. Prendre les candidats **dans l'ordre**, poser le claim avant chaque edition, livrer, puis passer au suivant sans attendre review, CI, DWELL ou merge du precedent ; une issue servie repart en queue d'elle-meme. Le tapis ne refuse jamais, et la lane ne re-trie pas : pas de preference de famille ou de serie a elle, et pas de repli sur une EPIC "maison". Un candidat ne se saute que pour une barriere reelle (GPU-only, vision-only, second LIGHT du meme genre d'affilee selon G-VAR-3), dite dans le rapport de cycle, et l'issue sautee reste en tete pour le tirage suivant ; un claim vivant d'une autre lane est deja retenu par le tapis. Un EPIC se sert par un sous-grain, jamais par un claim de l'EPIC entier : le tapis imprime sa procedure et la commande `--paths`. L'ancien `pick_idle_grain.py` ne choisit plus le grain et n'est plus une voie de repli (#26926) ; il reste un outil de diagnostic (`--orphans-report`). Regles completes : [proactive-coordination.md](../rules/proactive-coordination.md) (plancher multi-grain, "rien a faire" avec >0 issues ouvertes = echec de methode).

### Phase 2bis : Ne jamais bloquer (mandat user 07/10, session directe po-2026)

Aucune attente externe — CI, review, DWELL, merge, reponse d'une autre lane, run long — n'arrete la lane. Une verification non concluable a l'instant s'ecrit dans le **registre des verifications en attente** de la memoire du workspace (`pending-checks-registry.md`, indexe dans `MEMORY.md`) : `quoi | ou | geste si concluant | posee le`. Le cycle suivant l'ouvre en debut de session, verifie les lignes echues, vide les resolues — c'est une **restitution**, pas une interruption.

- **Pas de watcher long.** Un `run_in_background` plus long que le cycle (30 min) immobilise la session au lieu de la faire produire : le cycle suivant verifiera gratuitement depuis le registre. Watchers toleres : uniquement courts (quelques minutes), quand la suite du travail en depend directement dans la meme fenetre.
- **Parallelisme** : sous-agents (`run_in_background: true`), appels sk-agent, scripts en arriere-plan — la session principale reste productive pendant ce temps.
- **Un seul observateur** par condition asynchrone ; ne jamais poller en parallele d'une notification existante, et couvrir succes, echec, annulation et terminaison inattendue.
- **Etat durable dans les memoires, les dashboards RooSync et git** — jamais dans la memoire vive d'une instance, qui meurt avec elle.

### Phase 3 : Travailler et livrer

- Une issue creee par la lane **nomme son parent** dans son body (`Part of #N` : l'EPIC ou l'issue de serie), ou ecrit `Sans parent : <raison>`. Ce lien fait avancer le parent sur le tapis et rend l'issue visible a la consolidation de sa serie.
- Une PR = un sujet ([catalog-pr-hygiene](../rules/catalog-pr-hygiene.md) : catalogue byte-identique a main, `Closes #N` seulement si l'issue est entierement resolue, sinon `See #N`).
- Notebooks : C.1 (pas d'erreur volontaire), C.2 (commit AVEC outputs, re-exec des cellules modifiees), H.3 (pre-commit) — cf [notebook-conventions.md](../rules/notebook-conventions.md).
- Vrai outil SOTA, jamais workaround degrade ([sota-not-workaround.md](../rules/sota-not-workaround.md)) ; env casse = reparer, pas contourner (regle F).
- Skills/sous-agents specialises quand ils existent : [docs/reference/subagents-reference.md](../../docs/reference/subagents-reference.md).
- Avant d'impliquer reviewer, adjoint ou coordinateur, reproduire tout rouge propre a la PR, corriger sa cause et relancer les tests/gates pertinents. Un reviewer valide un livrable deja teste ; il ne sert jamais de premier test-runner. Un rouge confirme sur `main` est signale comme base-inherited avec preuve **et avec le numero de l'issue `[main-red]`** qui porte la cause, puis la lane poursuit sa file.

### Phase 4 : Avant de terminer (obligatoire)

1. **Commit + PR AVANT le rapport** — jamais de [DONE] sur un travail non commite.
2. `[DONE]` lane-specific sur le dashboard workspace (resume : livrables, PRs, residuel). Une PR livree ne clot jamais la session : poursuivre la file puis re-piocher jusqu'a la fin effective de la session.
3. Bloqueur nécessitant une action user : l'inscrire dans le registre durable, puis restituer les questions ouvertes en un seul bloc en fin de session ([user-blocker-signaling](../rules/user-blocker-signaling.md)). Le **registre des verifications en attente** (Phase 2bis) est relu dans le meme geste : lignes resolues retirees, lignes ouvertes conservees telles quelles — une verification en attente ne se perd pas entre deux cycles.
4. Repondre au DM coordinateur si une mission a ete traitee.
5. MAJ `MEMORY.md` si lecon durable (les PR#/SHA ephemeres vont au dashboard, pas en memoire).

## Notes

- Commande **sans parametre** : elle choisit automatiquement la tache suivante.
- Etat persistant : dashboards RooSync + issues GitHub + MEMORY.md.
- Jamais d'etat terminal-idle ("rien a faire", "await dispatch", "lane exhausted") : le pool global est toujours ouvert.
