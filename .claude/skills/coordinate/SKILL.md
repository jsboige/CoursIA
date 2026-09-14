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

## Budget de cycle (HARD — mandat user 2026-09-14)

1. **Un cycle tient en 1 h a 1 h 30 de travail entre deux crons de 4 h**, puis la session se rendort. Verbatim user : « Ca donne entre 1h et 1h30 max de travail entre 2 crons, c'est deja beaucoup je pense, et il ne faudrait pas depasser ca. Sinon c'est un defaut de delegation. »
2. **Decoupe interne des phases — EN ATTENTE DE MESURE.** Le user a recuse une decoupe chiffree posee au jugement : « sur les durees suggerees c'est au doigt mouille, hein, le mieux serait d'etudier ce qui a bien marche debut juillet quand on produisait beaucoup sans pour autant trop lesiner sur la qualite ». La mesure du regime de debut juillet (fenetre 2026-07-01 → 07-14) est deleguee a la lane `myia-ai-01:claudish` (DM `msg-20260914T195758-l93rsb`). **A REMPLACER par la decoupe mesuree — ne pas poser de chiffre au jugement.** Tant que cette mesure n'est pas rendue, aucune duree de phase n'est normative : les trois phases gardent leur ORDRE (grounding → dispatch → travail reel) sans budget chiffre.
3. **Mesurer le temps activement**, pas au ressenti : `date -u` en entree et en sortie de chaque phase ; le total du cycle est annonce dans le rapport de fin.
4. **Un depassement se traite en DELEGUANT**, jamais en rognant le grounding ou le dispatch.
5. **Tout ce qui est delegable EST delegue**, sans arbitrage au cas par cas. Attendre le cron suivant pour recuperer un resultat est gratuit — verbatim : « tu peux tout a fait attendre un cron pour economiser tes tokens, on n'est pas a 4h pres sauf crise a gerer ».
6. **Le contenu appartient au coordinateur adjoint** (`myia-po-2025:CoursIA-2`) : notebooks, series, pedagogie. ai-01 ne garde que les PRs de **CI et de harnais**. Entrer dans le corps d'une PR de contenu est par defaut une faute de budget.
7. **Les taches lourdes** (tests, builds lake, trainings, papermill) se lancent en arriere-plan **AU DEBUT de la phase de travail reel**, pour travailler en foreground pendant leur execution.

## Process

Les phases ci-dessous s'executent sous le budget defini par la section `## Budget de cycle` ci-dessus : 1 h a 1 h 30 de travail au total, tout depassement etant un defaut de delegation.

### Phase 1 - Contexte memoire

1. `~/.claude/projects/d--CoursIA/memory/MEMORY.md` — index + quick reference
2. `~/.claude/projects/d--CoursIA/memory/coordinator-durable-state.md` — axes directeurs, bloqueurs user, watches, calendrier
3. Au besoin : [docs/reference/cluster-agents.md](../../../docs/reference/cluster-agents.md) (machines, lanes, GPU), [docs/reference/teaching-context.md](../../../docs/reference/teaching-context.md) (calendrier ecoles)

### Phase 2 - Etat live

0. **Rester courant** : `git checkout main && git pull --ff-only` + `git submodule update --init` — le coordinateur travaille sur un main LOCAL a jour, jamais en grepant un working-tree stale ni en pilotant via `origin/*`.
1. **Dashboards (canal PRINCIPAL) — lire LES DEUX, independamment** : `roosync_dashboard(action:"read", type:"workspace", section:"all")` pour `workspace-CoursIA` **et** pour `workspace-CoursIA-2`. Deux lanes co-egales ; **aucune n'est "le dashboard du coordinateur"**. Une `lane` = machine x workspace : chaque machine avec une lane CoursIA-2 a AUSSI une lane CoursIA. Lire chacun separement pour ne rater aucun ASK/blocker.
2. **Inbox DM — drainer et EXTRAIRE, jamais survoler** : `roosync_messages(action:"inbox", status:"unread", deep:true)` — **sans `deep:true` le compte de non-lus est un faux zero**. Deux gestes, dans cet ordre. **(a) Purger les classes qui doublonnent une surface deja lue** — `bulk_mark_read(subject_contains:"Worker Report")` et `bulk_mark_read(subject_contains:"[MENTION] Dashboard")` : sans ca l'arriere se reconstruit a ~8 DM/h et noie le signal utile, qui pese moins de 10 % du volume. **(b) Extraire la liste nommee des PRs deja pre-machees** — marqueurs `[ADJOINT PREFLIGHT]`, `[ADJOINT VERIFIED]`, `[ADJOINT DECISION PACK]`, `preflight exact-head`. Cette liste est une **entree obligatoire de la Phase 3.3** : le pre-machage est produit qu'on le lise ou non ; non consomme, il est paye deux fois.
3. **GitHub** : `gh pr list --state open` (a merger) + le pool **tire, jamais scanne** — `python scripts/pick_idle_grain.py --lane myia-ai-01:CoursIA` (un `gh issue list` nu plafonne a 30, tries par recence : il ne montre que ce que je viens de creer, et c'est ce biais que le steering doit eviter de reproduire).
4. **Cron** : `CronList` — si le job coordinateur a disparu (session-only), re-armer `CronCreate("13 0-23/2 * * *", "/coordinate", recurring)`. Cadence unique, PAS de 2e cron ni ScheduleWakeup en plus.

### Phase 3 - Dispatchs, relances, memoire (LES 30 PREMIERES MINUTES)

**Cette phase precede la passe de merge et se ferme avant elle.** L'ordre inverse -- merger d'abord, dispatcher avec ce qui reste -- ne termine jamais : le pool de PRs est non borne et chaque PR ouvre trois surfaces a lire, donc les lanes sont affamees **par construction du cycle**, pas par negligence. Le symptome mesure : un cycle de plus de 4 h pour une cadence de 4 h, passe a rejouer le travail deja fait par l'adjoint et les bots (correction user 2026-09-14).

1. **Sweep unique, trie par anciennete** -- il sert LES DEUX phases, on ne le capture qu'une fois : `gh pr list --state open --limit 200 --json number,title,author,createdAt,mergeStateStatus,reviewDecision,headRefOid --jq 'sort_by(.createdAt) | .[] | [.createdAt[0:10],.number,.mergeStateStatus,.reviewDecision,.title] | @tsv'`. Sans `--limit`, gh plafonne a 30, et sans tri declare il rend par recence. **Pas de champ `reviews`** (payload lourd -- 504). 200 lignes rendues = plafond touche, paginer plutot que croire la liste complete.
2. **Grouper LA QUEUE par lane, et dispatcher le deblocage.** Les ~20 PRs les plus vieilles, regroupees par leur tag `Grain: ... lane`, partent en mandat de deblocage a leur lane. Une PR est vieille **parce qu'**elle est bloquee : ce qui se dispatche est le deblocage, pas le merge qui s'attend. Le lot d'une lane se derive du sweep seul -- aucun re-audit prealable n'est requis pour l'envoyer.
3. **Relancer les nits bloquants, nommement.** Chaque reserve non levee (`[Hermes] COMMENT_WITH_CONCERNS`, `CHANGES_REQUESTED`, nit user, thread inline non resolu) est renvoyee a la lane de l'auteur de la PR **avec le point cite**. Une reserve qu'on ne relance pas devient un grain qu'aucune lane ne sait qu'elle doit executer -- et celles posees par ai-01 ne peuvent etre levees par personne d'autre.
4. **Le rouge sans lane est a MOI.** Le garde "reparer son rouge d'abord" ([proactive-coordination](../../rules/proactive-coordination.md) R5) renvoie chaque lane sur ses propres PRs bloquees -- mais une PR **sans tag `Grain:` lisible** n'est imputable a aucune lane et reste invisible a tous les gardes. Lire le commentaire marker-guarde `GRAIN-ORPHANS-SWEEP` sur #13086 (rafraichi via `python scripts/pick_idle_grain.py --orphans-report`) et traiter chaque orpheline nommee avec son auteur : reparer, dispatcher nommement, ou fermer en le disant. Le coordinateur est soumis au meme garde pour **sa propre** lane.
5. **Trancher les design-gates en attente** dans le cycle -- ne pas deferer une option deja investiguee. Regles : [coordinator-discipline.md](../../rules/coordinator-discipline.md) (R3 lanes independantes, R4 jamais sanctionner l'idle, R5 steer qui ATTEINT/VRAI/DECIDE).
6. **Grounder chaque grain firsthand** (`gh issue view N` / `gh pr view N`) AVANT de dispatcher -- jamais depuis un status condense.
7. **Double canal obligatoire** : DM `roosync_messages(action:"send", to:"<machine>:<workspace>", ...)` (le worker lit l'inbox en premier, le DM survit a la condensation) **+** pointeur `[DISPATCH->inbox]` sur le dashboard de la lane (sonnette persistante).
8. **Une lane sans grain = echec coordinateur** : deep-queue, fallback perenne par famille, ou pool global -- jamais un statut terminal-idle. Chaque worker draine **tous** ses nits et reserves reparables sur **toutes** ses PRs, puis enchaine plusieurs grains DEEP/MED ; une seule PR livree ne clot pas sa session.
9. **MAJ memoire maintenant, pas en fin de cycle** : `coordinator-durable-state.md` si l'etat durable a bouge. Repoussee a la fin, elle saute quand le cycle deborde -- et le cycle suivant re-derive ce qu'il savait deja.

**Budget** : ces neuf points sont **clos avant** d'ouvrir la Phase 4. S'ils ne le sont pas a la fin des 30 minutes, ce sont eux qu'on termine -- pas le merge qu'on commence.

### Phase 4 - Merge PAR LA QUEUE, sur dossiers premaches

**Ordre unique : du plus ancien au plus recent.** Selectionner les PRs CLEAN / vertes / `rc=0` selectionne les PRs **neuves par construction** : une PR est verte parce qu'elle est recente, et vieille parce qu'elle est bloquee. Merger la tete **degrade en plus la queue** -- un merge rend DIRTY les PRs ouvertes qui touchent les memes fichiers (mesure : le merge de #15627 a sali #15799 et #15915). Mandat user 2026-09-14 : merger en batch par la queue, en mandatant le deblocage aux workers.

**Ce que le coordinateur NE refait PAS.** L'audit d'Hermes, de NanoClaw et de l'adjoint **est deja fait** : il se lit, il ne se rejoue pas. Ne sont verifies que (a) le **delta** depuis la derniere review -- les commits pousses apres, qui ne levent rien par eux-memes (B.0 : une phrase leve, pas un SHA) ; (b) les **reserves non levees** ; (c) la **preuve decisive** du claim central. Dix allers-retours sur une PR ne coutent rien tant qu'on ne les reverifie pas dix fois.

1. **Exploiter les verdicts deja poses** : `[Hermes] COMMENT_WITH_CONCERNS` (prefixe de `reviews[].body`), `EXEC_PROVED` / `STRUCTURAL_ONLY` / `SUSPECT_REGRESSION` (body). Tout finding NanoClaw suit [audit-reassessment.md](../../rules/audit-reassessment.md) avant fix (~60 % de FP).
2. **Dossiers en parallele, decision sequentielle au coordinateur** : les PRs proches de decision partent en preparation `run_in_background: true` -- modele explicite obligatoire, haiku pour le mecanique, sonnet pour l'interpretation bornee ([model-delegation.md](../../rules/model-delegation.md)). **Le lot de chaque sous-agent est une liste explicite de numeros extraite du sweep de la Phase 3** -- jamais d'enumeration du pool par le sous-agent (des partitions recalculees se recouvrent). Dossier attendu : preuves citees (file:line, log, SHA), verdict par critere, questions ouvertes. Un dossier insuffisant repart avec UNE question precise -- jamais un re-audit integral par reflexe.
3. **Lecture B.0 personnelle avant chaque merge -- non delegable** : body + comments + reviews + diff ("Read Body Before Any Action") ; etat A L'INSTANT-T via `gh pr view N --json state,mergedAt,mergeStateStatus,reviews` (jamais depuis le dashboard ni le cycle N-1) ; organe `python scripts/check_unaddressed_nits.py <PR>` (exit 1 = ne pas merger ; son vert ne dispense pas de la lecture). Une levee porte un auteur et une heure.
4. **Gates** : H.4 (notebooks : checkout + Papermill local OU log dans le body), catalogue byte-identique a main (`gh pr view N --json files`), scope reel = titre.
5. **Merge** : sous `myia-ai-01` (droit `MergePullRequest` verifie firsthand 2026-08-08), `--squash` par defaut, `--merge` (preserve-SHA) pour la base d'un stack, **JAMAIS `--delete-branch`**.

### Phase 5 - Fin de cycle (obligatoire)

1. **Commit + PR AVANT le rapport** — ne jamais annoncer un travail non commite.
2. `[DONE]` lane-specific sur **les deux** dashboards (jamais un miroir copie-colle).
3. **Bloqueurs user** : re-poke explicite dans vscode a CHAQUE fin de session tant que l'action user n'est pas faite ([user-blocker-signaling](../../rules/user-blocker-signaling.md)).
4. MAJ `coordinator-durable-state.md` si l'etat durable a change (PR#/SHA ephemeres → dashboard, pas la memoire).
5. **Une seule investigation par cycle, et en fin de session.** Toute question ouverte qui n'est **pas** un bloqueur de merge se note et attend le cycle suivant : mesurer un organe, verifier une provenance, instruire un doute de securite sont des gestes utiles et couteux, qui n'ont leur place qu'apres les dispatchs, les relances et la passe de merge. Une investigation qui deborde sur le cycle suivant est une investigation de trop -- elle a mange le temps des lanes. Si l'objet est reellement urgent, il devient un **grain dispatche**, pas une enquete du coordinateur.

## Regles importantes

- **Force push** : jamais sur `main` ; autorisé sur une branche de PR à lane unique — cf [git-workflow.md](../../rules/git-workflow.md)
- **Coordination via RooSync uniquement** — aucun fichier de coordination/rapport dans git
- **Deux dashboards workspace, coordonnes independamment** — `workspace-CoursIA` et `workspace-CoursIA-2` sont co-egaux ; lire et poster un contenu lane-specific sur CHACUN a chaque cycle, jamais de broadcast miroir, jamais "le mien vs celui des workers".
- **Issues + PRs** — chaque tache = issue, chaque livraison = PR avec review
- **Priorites courantes** : vivre dans `coordinator-durable-state.md` (memoire) + dashboards — pas dans ce fichier (harness-hygiene : le skill decrit le processus, pas l'etat).
