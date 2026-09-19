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
2. **Decoupe interne des phases — EN ATTENTE DE MESURE.** Le user a recuse une decoupe chiffree posee au jugement : « sur les durees suggerees c'est au doigt mouille, hein, le mieux serait d'etudier ce qui a bien marche debut juillet quand on produisait beaucoup sans pour autant trop lesiner sur la qualite ». La mesure du regime de debut juillet (fenetre 2026-07-01 → 07-14) est deleguee a la lane `myia-ai-01:claudish` (DM `msg-20260914T195758-l93rsb`). **A REMPLACER par la decoupe mesuree — ne pas poser de chiffre au jugement.** Tant que cette mesure n'est pas rendue, aucune duree de phase n'est normative : les quatre phases gardent leur ORDRE (queue READY → merges → dispatchs → travail non delegable) sans budget chiffre.
3. **Mesurer le temps activement**, pas au ressenti : `date -u` en entree et en sortie de chaque phase ; le total du cycle est annonce dans le rapport de fin.
4. **Un depassement se traite en DELEGUANT**, jamais en rognant le grounding ou le dispatch.
5. **Tout ce qui est delegable EST delegue**, sans arbitrage au cas par cas. Attendre le cron suivant pour recuperer un resultat est gratuit — verbatim : « tu peux tout a fait attendre un cron pour economiser tes tokens, on n'est pas a 4h pres sauf crise a gerer ».
6. **Le contenu appartient au coordinateur adjoint** (`myia-po-2025:CoursIA-2`) : notebooks, series, pedagogie. ai-01 ne garde que les PRs de **CI et de harnais**. Entrer dans le corps d'une PR de contenu est par defaut une faute de budget.
7. **Les taches lourdes** (tests, builds lake, trainings, papermill) se lancent en arriere-plan **AU DEBUT de la phase de travail reel**, pour travailler en foreground pendant leur execution.

## Process

Les phases A-D s'executent dans cet ordre sous le budget total de 1 h a 1 h 30. La file READY est preparee inter-cycle : la reconstruire par un sweep manuel au debut annule le travail de l'adjoint.

### Phase A - Deriver les deux files executables une fois

1. Lire l'index memoire et `coordinator-durable-state.md`, puis les deux dashboards workspace et l'inbox `deep:true`. Relever les non-lus et les PRs en attente avant toute lecture de fichier.
2. Verifier le cron unique. Ne pas bouger le checkout partage s'il est sale : travailler depuis `main` frais dans un worktree isole si necessaire.
3. Extraire les numeros explicitement prepares par l'adjoint et lancer **une fois** : `python scripts/check_adjoint_prevalidation.py --queue <PR...>`. La sortie JSON est derivee oldest-first, sans registre persistant.
4. `REVIEW_READY` entre en Phase B0 : toutes les portes prémâchées sont vertes, seule la review exact-head manque. `READY`/`MERGE_READY` entre en Phase B1. `DWELL_PENDING`, `STALE` et les vrais `BLOCKED` portent leur événement de reprise. Exit 2 est UNKNOWN fail-closed.
5. **L'adjoint est un producteur continu, jamais un waiter.** Après avoir émis `REVIEW_READY`, il poursuit les candidates suivantes, refreshs, extensions et préparations conditionnelles. Il consomme les reviews ai-01 comme événements entrants et republie les dossiers finals, sans suspendre sa cadence ni attendre la fin de Phase B0.

### Phase B0 - Reviewer en rafale la file REVIEW_READY

1. Parcourir `REVIEW_READY` oldest-first. Lire personnellement body, tous les commentaires, corps/états des reviews, threads et diff ; exploiter le dossier prémâché sans rejouer les audits déjà étayés.
2. Poser la disposition formelle exact-head immédiatement (APPROVED ou CHANGES_REQUESTED motivée). Une absence d'approval n'est jamais redispatchée comme attente worker : c'est du travail local ai-01.
3. Chaque APPROVED est un événement pour l'adjoint, qui finalise le dossier en parallèle. Continuer la rafale sans attendre chaque republication individuellement ; les dossiers finals alimentent Phase B1 dès qu'ils arrivent.

### Phase B1 - Consommer et merger en rafale

1. Parcourir les `READY` oldest-first, y compris celles générées pendant Phase B0. Juste avant la lecture personnelle, lancer `python scripts/check_adjoint_prevalidation.py --consume <PR>` : cette commande relit toutes les surfaces live et ne reutilise aucun cache de `--queue`.
2. **Exit 0 seulement** ouvre la lecture B.0 personnelle minimale : body, commentaires, corps/etats des reviews, threads et diff. Lire `tail_to_read`, le delta et la preuve decisive ; ne pas rejouer l'audit complet de l'adjoint, d'Hermes ou de NanoClaw.
3. Repasser `python scripts/check_unaddressed_nits.py <PR>`, latest-wins CI, H.4, catalogue byte-identique a main, scope, stack et variation. Un preflight READY n'autorise jamais a lui seul le merge.
4. Merger avec le `head` retourne par **ce** `--consume` : `gh pr merge <PR> --repo jsboige/CoursIA --squash --match-head-commit <HEAD>`. Jamais `--delete-branch`. Recalculer la variation apres chaque merge pertinent.
5. Toute mutation ou insuffisance expulse la candidate vers la Phase C ; elle ne transforme pas la rafale en investigation.

### Phase C - Dispatcher massivement les sorties et le travail lourd

1. Regrouper `STALE`/vrais `BLOCKED` et les rouges par lane ; citer la cause exacte et l'événement de reprise attendu. **Ne jamais dispatcher une simple absence d’APPROVED** : elle appartient à `REVIEW_READY` et à la rafale locale ai-01. Les dossiers invalides repartent vers l'adjoint, les réparations vers leur lane propriétaire.
2. Grounder chaque grain firsthand, poser le claim GitHub et utiliser le double canal DM + pointeur dashboard. Une lane sans grain recoit une deep-queue ou un fallback perenne ; elle n'attend jamais une candidate en HOLD, DWELL, CI ou review.
3. Les investigations lourdes, tests, builds et reconciliations sont dispatches maintenant afin que le prochain cycle retrouve une queue actionnable. Après la rafale seulement, exécuter `python scripts/pick_idle_grain.py --orphans-report` : toute PR hors radar de l'adjoint reçoit alors un propriétaire ou un événement de reprise sans retarder le premier merge. Mettre a jour la memoire durable si son etat a change.

### Phase D - Travail non delegable borne et fin de cycle

1. Garder seulement les decisions finales, arbitrages strategiques et lectures personnelles que personne ne peut signer a la place d'ai-01. Une seule investigation personnelle au maximum ; si elle est delegable ou deborde, elle devient un grain.
2. Consigner les metriques : READY recues, merges tentes/reussis, rejets par cause, heure du premier merge, temps avant passage aux dispatchs et dossiers republies apres staleness. Si une READY existe et qu'aucun premier merge n'est tente dans les 15 minutes, signaler l'alarme de derive.
3. Commit + PR avant rapport ; puis `[DONE]` lane-specific sur les deux dashboards. Restituer en bloc le registre des questions user ouvertes, sans interruption intermediaire ni liste parallele.

## Regles importantes

- **Force push** : jamais sur `main` ; autorisé sur une branche de PR à lane unique — cf [git-workflow.md](../../rules/git-workflow.md)
- **Coordination via RooSync uniquement** — aucun fichier de coordination/rapport dans git
- **Deux dashboards workspace, coordonnes independamment** — `workspace-CoursIA` et `workspace-CoursIA-2` sont co-egaux ; lire et poster un contenu lane-specific sur CHACUN a chaque cycle, jamais de broadcast miroir, jamais "le mien vs celui des workers".
- **Issues + PRs** — chaque tache = issue, chaque livraison = PR avec review
- **Priorites courantes** : vivre dans `coordinator-durable-state.md` (memoire) + dashboards — pas dans ce fichier (harness-hygiene : le skill decrit le processus, pas l'etat).
