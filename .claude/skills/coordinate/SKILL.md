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

0. **Rester courant** : `python scripts/coordination/session_hygiene.py` D'ABORD (exit 1 = au moins un ROUGE), puis `git checkout main && git pull --ff-only` + `git submodule update --init` — le coordinateur travaille sur un main LOCAL a jour, jamais en grepant un working-tree stale ni en pilotant via `origin/*`. **L'organe passe avant le geste parce que le geste peut ECHOUER EN SILENCE** : mesure du 18/09, `git checkout main` refusait depuis des jours (un worktree residuel detenait `main`), l'arbre est reste parke sur une branche de feature, et l'organe B.0 qu'on y lancait avait 437 lignes de moins que celui de `main` — assez pour inverser des verdicts de merge deja publies. `session_hygiene.py` couvre branche parkee (test d'identite de contenu, robuste au squash), `main` pris en otage par un worktree, derive des organes vs `origin/main`, fichier sensible non suivi ET non ignore, inflation de worktrees et stashes. Il **ne peut pas** voir l'inbox, les dashboards, les memoires ni les ledgers : il les rappelle nommement en fin de sortie, a faire a la main.

1. **Dashboards (canal PRINCIPAL) — ENUMERER d'abord, jamais lire une liste apprise par coeur** : `roosync_dashboard(action:"list")`, puis `read` avec `section:"all"` sur **chaque cle dont le workspace declare est pertinent**. Les lanes sont co-egales ; **aucune n'est "le dashboard du coordinateur"**. Une `lane` = machine x workspace : chaque machine avec une lane CoursIA-2 a AUSSI une lane CoursIA, et le trio titulaire/secretaire/coordinateur ajoute `CoursIA-3`. Lire chacune separement pour ne rater aucun ASK/blocker.

   **Pourquoi enumerer, et pas nommer** : une skill qui sait d'avance quoi lire est **structurellement aveugle** a une cle qu'elle n'anticipe pas. Le 2026-09-21, `workspace-CoursIA (2)` — cle forkee par collision de noms Google Drive — portait **23 messages vivants** de po-2026 et po-2027, dont deux PRs debloquees en attente du merge-gate, pendant plusieurs jours sans qu'aucun cycle ne la voie. Une cle a suffixe ` (N)` dont le `workspace` declare **ne porte pas** ce suffixe est une moitie de la meme lane, pas une lane voisine : la lire, et escalader la reparation (`action:"merge"`, cf dashboard `global`).

2. **Inbox DM — drainer et EXTRAIRE, jamais survoler** : `roosync_messages(action:"inbox", status:"unread", deep:true)` — **sans `deep:true` le compte de non-lus est un faux zero**. Deux gestes, dans cet ordre. **(a) Purger les classes qui doublonnent une surface deja lue** — `bulk_mark_read(subject_contains:"Worker Report")` et `bulk_mark_read(subject_contains:"[MENTION] Dashboard")` : sans ca l'arriere se reconstruit a ~8 DM/h et noie le signal utile, qui pese moins de 10 % du volume. **(b) Extraire la liste nommee des PRs deja pre-machees** — marqueurs `[ADJOINT PREFLIGHT]`, `[ADJOINT VERIFIED]`, `[ADJOINT DECISION PACK]`, `preflight exact-head`. Cette liste est une **entree obligatoire de la Phase 3.3** : le pre-machage est produit qu'on le lise ou non ; non consomme, il est paye deux fois.
3. **GitHub** : `gh pr list --state open` (a merger) + le pool **tire, jamais scanne** — `python scripts/pick_idle_grain.py --lane myia-ai-01:CoursIA` (un `gh issue list` nu plafonne a 30, tries par recence : il ne montre que ce que je viens de creer, et c'est ce biais que le steering doit eviter de reproduire).
4. **Cron** : `CronList` — si le job coordinateur a disparu (session-only), re-armer `CronCreate("27 */4 * * *", "/coordinate", recurring)` — **4 h, minute off-`:00`** (mandat user 2026-09-13, crise de consommation Anthropic : le coordinateur doit etre le dernier agent a tourner sur le provider ; le jitter evite de frapper l'API a la meme seconde que le reste de la flotte). Cadence unique, PAS de 2e cron ni ScheduleWakeup en plus — un cycle plus long que sa cadence annule deja ses propres declenchements, en empiler un second ne fait qu'ajouter de la conso.

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

1. **Gate d'entree AVANT toute lecture personnelle (HARD)** : pour chaque candidate oldest-first, lancer `python scripts/check_adjoint_prevalidation.py <PR>`. Le gate repond a **deux** questions distinctes — *le dossier est-il integre ?* et *la PR est-elle mergeable ?* — et ne les confond plus (arbitrage #16800, sign-off user 2026-09-19) :

   | Sortie | Sens | Ce que fait ai-01 |
   |---|---|---|
   | **0** | dossier integre + `verdict: READY` | ouvrir body, commentaires, reviews, threads, diff ; lire B.0 ; merger si les gates du point 5 passent |
   | **3** | dossier integre + `verdict: BLOCKED` | **n'ouvrir AUCUNE surface** — dispatcher a la lane auteur depuis le motif atteste par le dossier, et passer a la candidate suivante |
   | **1** | pas de dossier digne de confiance (absent, malforme, perime, mauvaise lane/auteur, empreinte cassee) | router la candidate vers une lane **TIERCE qualifiante** -- l'adjoint `myia-po-2025:CoursIA-2` en premier, mais toute autre lane du cluster qui **ne porte pas** la PR convient (#16906) --, l'exclure jusqu'a un dossier exact-head, candidate suivante |
   | **2** | organe injoignable | refus fail-closed, identique a 1 |

   **Exit 3 n'est PAS un gate plus mou** : un dossier BLOCKED doit satisfaire toutes les exigences structurelles, `surfaces-sha256` comprise. Ce qui tombe, ce sont les controles qui **refutent une claim READY** (checks verts, B.0 clear, zero thread non resolu, non-draft) — ce sont des raisons pour lesquelles une PR est bloquee, pas des raisons de se mefier du dossier qui le dit.

   **Pourquoi** : exiger READY pour `exit 0` faisait dependre le **droit de lire** de l'**etat de mergeabilite**, donc ai-01 ne pouvait ouvrir que les PRs qui allaient deja bien — jamais les plus vieilles, qui sont vieilles *parce que* bloquees. Ca poussait aussi l'adjoint a ecrire READY pour seulement rendre son travail visible, ce qui a produit un faux `b0: clear` **mesure** sur une PR portant 3 findings HIGH ouverts (#16160).

   **Une seule identite est neutre** : `myia-ai-01`, et uniquement pour les surfaces qu'elle ecrit **apres** le dossier. Sans ca, le geste que le gate autorise — lire la PR, puis lever sa propre reserve — perime le dossier que le gate exige, et une PR bloquee par la seule reserve du coordinateur ne peut jamais se merger sans un aller-retour complet. Une surface de **tout autre auteur**, ou une surface `myia-ai-01` **anterieure** au dossier, perime toujours.

   Le bloc `[ADJOINT PREFLIGHT]` est genere par `python scripts/check_adjoint_prevalidation.py <PR> --template [--lane <machine:workspace>]`, puis complete par la lane emettrice -- **qui rend son PROPRE nom** : un dossier sous un nom d'emprunt defait le refus d'auto-attestation. Le compte des commentaires exclut le commentaire-dossier lui-meme. **Interdit de contourner le gate par un sous-agent, une lecture API directe ou un ancien dossier d'inbox.**
2. **Exploiter les verdicts deja poses** : `[Hermes] COMMENT_WITH_CONCERNS` (prefixe de `reviews[].body`), `EXEC_PROVED` / `STRUCTURAL_ONLY` / `SUSPECT_REGRESSION` (body). Tout finding NanoClaw suit [audit-reassessment.md](../../rules/audit-reassessment.md) avant fix (~60 % de FP).
3. **L'adjoint fabrique, ai-01 ne re-fabrique pas** : les PRs sans dossier valide partent en lots explicites issus du sweep vers l'adjoint, pas vers des sous-agents ai-01. Dossier attendu : contrat machine-lisible exact-head, trois surfaces B.0, checks latest-wins, scope, domaine et verdict ; un changement de head ou de surface le perime. L'adjoint vise **>=20 READY oldest-first par fenetre de 4 h quand >=20 candidates sont eligibles**, et remonte chaque READY immediatement : le lot n'est pas une barriere. Un dossier insuffisant repart avec UNE question precise. Le login GitHub `jsboige` etant partage, le champ `lane` est une declaration fail-closed, pas une preuve cryptographique d'identite. Ce que le gate exige est que la prevalidation soit **tierce**, pas qu'elle vienne d'une lane nommee : toute lane du cluster (`QUALIFYING_LANES`) peut emettre un dossier pour une PR **qu'elle ne porte pas**, et le gate refuse l'auto-attestation en comparant la lane du dossier au tag `Grain:` du body (#16906). Une lane hors de l'ensemble, ou malformee, echoue toujours ferme.
4. **Lecture B.0 personnelle minimale avant chaque merge -- non delegable, seulement APRES gate vert** : body + comments + reviews + diff ("Read Body Before Any Action") ; etat A L'INSTANT-T via `gh pr view N --json state,mergedAt,mergeStateStatus,reviews` (jamais depuis le dashboard ni le cycle N-1) ; organe `python scripts/check_unaddressed_nits.py <PR>` (exit 1 = ne pas merger ; son vert ne dispense pas de la lecture). Verifier seulement le dossier, le delta et la preuve decisive ; ne pas rejouer l'audit complet. Une levee porte un auteur et une heure.
5. **Gates de merge** : un preflight READY n'autorise jamais le merge. Appliquer encore B.0, latest-wins CI, H.4 (notebooks : checkout + Papermill local OU log dans le body), catalogue byte-identique a main (`gh pr view N --json files`), scope reel = titre, ordre de stack, variation et relecture de la queue de commentaires.
6. **Merge** : sous `myia-ai-01` (droit `MergePullRequest` verifie firsthand 2026-08-08), avec `gh pr merge <N> --repo jsboige/CoursIA --squash --match-head-commit <SHA>` (`--merge` preserve-SHA pour la base d'un stack), **JAMAIS `--delete-branch`**.

### Phase 5 - Fin de cycle (obligatoire)

1. **Commit + PR AVANT le rapport** — ne jamais annoncer un travail non commite.
2. `[DONE]` lane-specific sur **les deux** dashboards (jamais un miroir copie-colle).
3. **Bloqueurs user** : restituer en un bloc les questions ouvertes du registre durable ; aucun re-poke intermédiaire ni liste parallèle ([user-blocker-signaling](../../rules/user-blocker-signaling.md)).
4. MAJ `coordinator-durable-state.md` si l'etat durable a change (PR#/SHA ephemeres → dashboard, pas la memoire).
5. **Une seule investigation par cycle, et en fin de session.** Toute question ouverte qui n'est **pas** un bloqueur de merge se note et attend le cycle suivant : mesurer un organe, verifier une provenance, instruire un doute de securite sont des gestes utiles et couteux, qui n'ont leur place qu'apres les dispatchs, les relances et la passe de merge. Une investigation qui deborde sur le cycle suivant est une investigation de trop -- elle a mange le temps des lanes. Si l'objet est reellement urgent, il devient un **grain dispatche**, pas une enquete du coordinateur.

## Amelioration continue des skills (mandat user 2026-09-21)

Les skills du trio — `coordinate` (ai-01), `coordinate-adjoint` (titulaire), `adjoint-secretary` (secretaire) — sont sous controle de source. **Elles se relisent et se corrigent regulierement, comme du code**, pas seulement quand elles cassent.

- **A chaque cycle, si une mesure du cycle contredit une skill, la skill se corrige dans le meme cycle** — par PR, comme tout changement de harnais (CLAUDE.md §A : PR + sign-off user pour un changement normatif substantiel ; une correction factuelle n'exige pas de sign-off supplementaire).
- **Les trois defauts a chercher en priorite**, parce qu'ils sont muets :
  1. une **liste codee en dur** de ce qu'il faut lire (dashboards, lanes, organes) — elle ne voit pas ce qu'elle n'anticipe pas ;
  2. une **reference vers une branche** plutot que `main` — elle pointe un etat perime, et devient muette si la branche disparait ;
  3. un **geste reimplemente a la main** alors que `scripts/` porte l'organe (`pr_gate.py`, `merge_dwell.py`, `count_code_sorry.py`, `check_unaddressed_nits.py`). Avant d'ecrire du jq de verdict : `git grep` le geste dans `scripts/`. Une approximation maison est biaisee vers l'accusation.
- **Une skill est datee de sa redaction**, exactement comme un body d'issue : la suspecter d'abord quand elle fait ATTENDRE ou RENONCER.
- Les suggestions faites a une skill d'autrui se postent **en commentaire de PR**, pas en `CHANGES_REQUESTED` : bloquer garderait la skill hors du controle de source, soit l'inverse du but.

## Regles importantes

- **Force push** : jamais sur `main` ; autorisé sur une branche de PR à lane unique — cf [git-workflow.md](../../rules/git-workflow.md)
- **Coordination via RooSync uniquement** — aucun fichier de coordination/rapport dans git
- **Dashboards workspace coordonnes independamment, et ENUMERES** — les cles se decouvrent par `action:"list"`, jamais par une liste codee en dur (cf Phase 2.1) ; lire et poster un contenu lane-specific sur CHACUNE a chaque cycle, jamais de broadcast miroir, jamais "le mien vs celui des workers".
- **Issues + PRs** — chaque tache = issue, chaque livraison = PR avec review
- **Priorites courantes** : vivre dans `coordinator-durable-state.md` (memoire) + dashboards — pas dans ce fichier (harness-hygiene : le skill decrit le processus, pas l'etat).
