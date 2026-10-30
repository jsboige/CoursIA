# Controleur de debordement CI (phase B) — `CI_OVERFLOW_LOCAL`

Volet 1 de [#22937](https://github.com/jsboige/CoursIA/issues/22937) : la **phase B** de la repartition hebergee / local.

## Ce que la variable decide

La **phase A** ([#22921](https://github.com/jsboige/CoursIA/pull/22921)) a pose la **forme hybride** des workflows de garde : une seule variable de depot, `CI_OVERFLOW_LOCAL`, decide si un job part sur le parc local (legende Linux) ou sur l'offre GitHub-hosted.

```yaml
runs-on: ${{ (github.event.pull_request.head.repo.full_name == github.repository && vars.CI_OVERFLOW_LOCAL == 'true') && fromJSON('["self-hosted","coursia-ephemeral","coursia-linux"]') || 'ubuntu-latest' }}
```

- variable a `true` -> PR meme-depot : jambe **locale** ;
- variable absente ou a `false` -> **GitHub-hosted** ;
- les forks, le `workflow_dispatch` et les crons restent heberges (la garde est liee a l'evenement `pull_request`).

La phase A est **manuelle** (un operateur pose la variable). La phase B, decrite ici, la **pilote**.

## La regle de decision

| etat mesure | decision |
|---|---|
| offre hebergee **saturee** (au moins `--saturation-jobs` jobs `ubuntu-latest` en file depuis plus de `--saturation-minutes`) **et** parc local libre (au moins `--min-free-slots` slots en ligne **et libres**) | variable a `true` |
| **charge rendue de la cohorte dans la marge hebergee** : l'offre hebergee n'attend pas, la marge (`--hosted-cap` moins les jobs heberges en file et en cours) est strictement positive, et la charge que la **cohorte** rend tient dans cette marge -- confirmee sur une **seconde** lecture | variable a `false` |
| parc local **lui-meme affame** (des jobs `coursia-linux` attendent) | variable a `false` (on rend la main a l'heberge) |
| **cohorte non etablie** (liste derivee du depot vide ou illisible) | **UNREADABLE** (aucune ecriture) |
| sinon (1 ou 2 jobs ages : bande morte) | **HOLD** (rien n'est ecrit) |

### La liberation mesure la COHORTE dans la MARGE hebergee (#22937 vague 3)

La liberation rend la **cohorte** a l'offre hebergee : les jobs dont le workflow lit
`vars.CI_OVERFLOW_LOCAL`, et eux seuls. Deux grandeurs, une comparaison :

1. **charge rendue** : les jobs **en file et en cours** sur le parc local dont le run
   appartient a un workflow de la cohorte (le chemin du workflow est deja dans la
   reponse des runs : le filtre ne coute aucun appel de plus) ;
2. **marge hebergee** : le plafond de l'offre (`--hosted-cap`, 20 ; mesure : 19 jobs
   heberges en concurrence au pic du 2026-10-16) moins les jobs heberges **en file et
   en cours** ;
3. **liberation** quand la charge rendue **confirmee** est **au plus egale** a la
   marge -- c'est-a-dire quand les **deux** lectures de la charge rendue tiennent dans
   la marge. C'est la lecture la plus haute qui decide, jamais la plus basse.

Les jobs **statiques** du parc n'entrent dans **aucun** des deux cotes : ils portent le
meme jeu de labels que la cohorte (`[self-hosted, coursia-ephemeral, coursia-linux]`)
mais leur workflow ne lit pas la variable, et ils ne reviendront jamais sur l'offre
hebergee. Les compter comme charge rendue etait le defaut de la vague 2 : des trois
jobs statiques en cours -- le regime normal d'une journee de PRs -- la liberation
n'avait plus jamais lieu, la variable restait a `true` et la cohorte tournait en local
meme quand l'heberge etait vide. Le pendule de la version precedente etait devenu un
**verrou** (review du coordinateur, 28/10 : les workflows qui lisent
`CI_OVERFLOW_LOCAL` gardent un `runs-on` statique sur le pool local).

#### D'ou vient la liste de la cohorte

Elle est **derivee du depot a chaque passage** (`derive_cohort_workflows`) : un fichier
de `.github/workflows/` est de la cohorte quand son contenu lit
`vars.CI_OVERFLOW_LOCAL` -- la forme que
`scripts/ci/check_self_hosted_runner_policy.py` enumere
(`HYBRID_RUNS_ON_OVERFLOW_GUARD`). Rien n'est recopie : un workflow qui rejoint la
forme hybride entre dans le calcul, un workflow qui la quitte en sort.

Le marqueur porte le prefixe `vars.` a dessein : le simple nom de la variable apparait
aussi dans la prose, et ranger son propre workflow dans la cohorte compterait un job
**statique** du parc comme charge rendue. Les lignes entierement commentaires sont
retirees avant la recherche, pour la meme raison : un en-tete qui cite la forme exacte
(`vars.CI_OVERFLOW_LOCAL`) ne fait pas du workflow un membre de la cohorte. Le job de
ce workflow, dont le `runs-on` est statique sur le pool local, n'est donc jamais dans
la cohorte qu'il mesure -- verifie sur le depot : les workflows derives excluent le
controleur lui-meme, qui cite la variable sans la lire.

Une liste **vide** ou **illisible** (repertoire absent, fichier non lisible) n'est pas
« une cohorte qui ne rend rien » : c'est une mesure **illisible**, et le verdict est
`UNREADABLE`, jamais une liberation. Le `sparse-checkout` du workflow garde donc
`.github/workflows` : sans ces fichiers, la liste serait vide a chaque passage.

#### La confirmation

Une seule lecture peut tomber sur un instant vide (le parc vient de finir un lot) : la
charge rendue est relue **par la meme methode**, espacee de `--confirm-seconds` (30 s).
Une confirmation absente, illisible ou tronquee bloque la liberation (fail-CLOSED).

#### Pourquoi la seule lecture « l'offre hebergee n'attend pas » ne suffit pas

Pendant que la cohorte tourne en local, l'offre hebergee ne porte **que** les jobs
hors debordement (CodeQL en setup par defaut, Lean CI, les advisories de starvation).
Elle parait donc **allegee**, meme quand la charge de la cohorte est enorme. Liberer
sur cette seule lecture rend la cohorte entiere a une offre qui s'etouffe derriere,
et le dwell de 90 min interdit ensuite de revenir a `true` : **on rejoue la nuit du
27/10** (reserve du coordinateur, 28/10). La lecture de l'offre ne suffit donc pas :
il faut celle de la charge rendue, qui est la seule a la borner.

C'est aussi pour cela que la premiere version (file hebergee **videe**) etait
inatteignable : le depot porte toujours des jobs heberges hors debordement, donc la
variable ne pouvait plus jamais revenir a `false` une fois posee -- le controleur
etait un **commutateur a sens unique**.

#### Le dwell : oppose a la liberation, deroge pour la re-absorption

Un **dwell** de `--dwell-minutes` (90 par defaut) interdit deux bascules rapprochees :
une variable qui oscille est pire qu'une variable stable. Le dwell est **coherent
avec la cadence** : il la depasse (90 > 60 min), sinon il ne peut jamais opposer quoi
que ce soit -- deux passages consecutifs d'un cron horaire sont toujours a plus de
60 min, et un dwell de 30 min etait donc inerte (point Hermes du 2026-10-27, 12:53Z).

La **liberation** n'echappe jamais au dwell : c'est elle qui fait revenir la cohorte,
donc c'est elle qui doit rester freinee.

La **re-absorption** (offre hebergee -> parc local) y echappe quand le backlog
heberge est **dur** : le plus ancien job attend depuis plus de `--panic-minutes`
(30 min par defaut). La nuit du 27/10, la liberation a rendu la cohorte a une offre
qui s'etouffee ensuite, et le dwell de 90 min a interdit de revenir a `true` : la
file a starve pendant toute la fenetre. Attendre 90 min devant une starvation
etablie prolonge la panne.

Cet echappement ne peut pas creer d'oscillation : il exige un backlog **dur** (le
plus ancien job attend), ce qui est **incompatible** avec la premise de liberation
(« l'offre hebergee n'attend pas ») -- les deux ne peuvent pas etre vraies a la meme
lecture.

L'organe est **fail-CLOSED** : une mesure illisible (listing incomplet, inventaire des runners inaccessible, liste de la cohorte vide ou illisible) ne produit **aucune** ecriture.

Une lecture **tronquee** (budget de lecture atteint) n'est pas une mesure illisible : c'est une mesure **partielle**, dont les comptes sont des bornes **inferieures**. La regle appliquee est **directionnelle** -- une borne inferieure etablit une affirmation **positive** (« au moins N jobs ages ») mais **n'etablit aucune affirmation negative** (« aucun job en file », « le parc local n'est pas affame », « la charge rendue tient dans la marge ») :

| lecture tronquee | conclusion bloquee | conclusion conservee |
|---|---|---|
| offre hebergee | « l'offre hebergee **n'attend pas** » -> pas de bascule vers `false` · une **marge** tiree d'un compte en cours borne -> pas de bascule vers `false` | « l'offre hebergee est **saturee** » -> la bascule vers `true` reste possible |
| parc local | « le parc local **n'est pas affame** » -> pas de bascule vers `true` | « le parc local **est affame** » -> la bascule vers `false` reste possible |
| charge rendue de la cohorte | « la charge rendue **tient dans la marge** » -> pas de bascule vers `false` | aucune : cette mesure ne sert qu'a liberer |

Mesure du 2026-10-27 sur la file reelle, avant correction : lecture hebergee complete (`budget_unread = 0`) mais lecture **locale tronquee a 15 runs**, ages de 15 a 20 min -- donc **au-dessus** du seuil de 15 min, donc desertes par une lecture complete. Le compte `starved = 0` etait alors une **borne inferieure** : « le parc local n'est pas affame » n'etait pas etabli, et la garde de securite s'ouvrait en faux. Le budget local a ete aligne sur le budget hebergee (40 -> 120) pour que la lecture locale soit complete dans le regime nominal : a 40, le parc local (44 a 55 runs eligibles mesures) etait a la limite exacte du plafond, donc la troncature etait une loterie.

## Usage

```bash
# verdict seul (defaut : dry-run, aucune ecriture)
python scripts/ci/ci_overflow_controller.py --repo jsboige/CoursIA --json

# application effective (le jeton d'ecriture est obligatoire)
ACTIONS_VARIABLES_PAT=... python scripts/ci/ci_overflow_controller.py \
  --repo jsboige/CoursIA --apply --json
```

Codes de retour : `0` nominal (HOLD ou bascule), `1` mesure illisible ou **etat de la variable illisible** (`UNREADABLE`), `2` refus (`REFUSED` : jeton de mesure absent, ou ecriture refusee par le depot).

### Les seuils de la liberation

| option | defaut | role |
|---|---|---|
| `--hosted-cap` | 20 | plafond de concurrence de l'offre hebergee (mesure : 19 jobs en concurrence au pic du 2026-10-16). La **marge** est ce plafond moins les jobs heberges en file et en cours ; la liberation exige que la charge rendue de la cohorte tienne dans cette marge |
| `--confirm-seconds` | 30 | pause avant la **seconde** lecture de la charge rendue de la cohorte, qui la confirme |
| `--panic-minutes` | 30 | age du plus ancien job heberge au-dela duquel le backlog est **dur** : la re-absorption n'est alors plus differee par le dwell |

## Jeton d'inventaire du parc (`RUNNERS_READ_PAT`)

`github.token` **ne porte pas** le droit de lire `/actions/runners` : aucune portee de `permissions:` ne le donne (la lecture d'inventaire exige un jeton d'administration). Le workflow expose donc `RUNNERS_READ_PAT` a cote de `GH_TOKEN`, **exactement la forme des six workflows freres** (`linux-runner-starvation-advisory.yml:107-109`, `coursia-waiter-starvation-advisory.yml:89`, `runner-starvation-advisory.yml:115`, `runner-coresidence-advisory.yml:97`, `quarto-pages-deploy.yml:149`) : secret de depot **read-only** (`Administration:read`, incapable de minter un registration-token, par design). L'organe accepte un jeton dedie via `--runners-token-env` (defaut `RUNNERS_READ_PAT`).

Cet usage est un **troisieme canal**, distinct des deux autres : il ne mesure ni la file ni la variable, il ne porte aucun droit d'ecriture.

En **local**, l'operateur n'a rien a poser : le jeton `jsboige` a le droit sur l'inventaire, et l'organe retombe sur le jeton courant quand aucun jeton dedie n'est present. **Secret absent** : le verdict vaut `UNREADABLE` et la raison nomme « jeton d'inventaire des runners absent (RUNNERS_READ_PAT) » -- jamais un `OK` par defaut (test `test_cli_sans_jeton_d_inventaire_sort_unreadable_nomme`).

## Qui ecrit — arbitrage (a) du user (c.6441695482, 27/10)

**Le workflow automatise ecrit la variable.** Option (a) de l'arbitrage user du 2026-10-27 : le secret `ACTIONS_VARIABLES_PAT` existe dans Actions (pose le 2026-10-27T17:05:48Z) et porte le droit fin `Variables: read-write` sur `jsboige/CoursIA` **seul** (expiration **2027-10-27**, valeur regeneree le 2026-10-27T17:24:12Z ; la date 2027-01-25 citee precedemment etait anterieure a la regeneration). Cette expiration n'est **pas exposee par l'API Actions** sur ce depot — `expiration_timestamp` y vaut `null` pour les trois secrets du depot — : elle est tenue par le coordinateur, qui en assure le renouvellement. Il est expose **au seul pas qui ecrit la variable** : ni le checkout ni le `setup-python` ne le voient.

Les portees du job restent `actions: read` + `contents: read` : la portee `variables` **n'existe pas** dans la liste des portees admises sous `permissions:` (reference de syntaxe des workflows GitHub : actions, attestations, checks, contents, deployments, discussions, id-token, issues, packages, pages, pull-requests, security-events, statuses). Une cle hors liste rend le fichier entier invalide : la porter ici aurait suffi a empecher le workflow de demarrer. C'est donc un **PAT** qu'il faut, pas une portee.

### Deux canaux, jamais le meme

| canal | variable | droit | sert a |
|---|---|---|---|
| mesure | `GH_TOKEN` (= `github.token` dans le workflow) | `actions: read` | files de jobs, liste des runs |
| **ecriture** | `ACTIONS_VARIABLES_PAT` | `Variables: read-write` | lire et ecrire la variable de depot |
| inventaire | `RUNNERS_READ_PAT` | `Administration: read` | `/actions/runners` |

**Aucun repli.** Si le secret d'ecriture est absent ou vide, le controleur **rend son verdict, n'ecrit rien**, et le resume du job **nomme la cause** (ligne `DEGRADE:`). Il ne se rabat jamais sur le jeton de mesure : un jeton sans le droit n'est pas un jeton de secours, c'est une faute d'outillage. Idem si l'etat de la variable est illisible (ni l'etat courant ni le dwell ne sont verifiables) : le verdict est rendu, l'ecriture est refusee, la cause est nommee (tests `test_secret_absent_verdict_seul_et_aucune_ecriture`, `test_etat_inconnu_bloque_l_ecriture_meme_avec_le_secret_present`).

Le verdict est **toujours** rendu dans ces deux cas : c'est la difference entre un mode degrade **visible** et une panne muette. Le resume du job porte le verdict, la raison, l'etat des deux lectures et les degrades nommes ; le workflow emet une annotation `::warning::` des que le resume contient une ligne `DEGRADE:`.

### La bascule en local

La meme voie, pour l'operateur qui veut agir hors du workflow -- le jeton d'ecriture est pose par commande :

```bash
ACTIONS_VARIABLES_PAT=$(gh auth token --user jsboige) \
  python scripts/ci/ci_overflow_controller.py --repo jsboige/CoursIA --apply --json
```

### Ou cette commande tourne (point 2 de la review ai-01 du 2026-10-27)

Sur le **siege du coordinateur, `D:\CoursIA-wt-merge-ready`** : un worktree detache, ramene sur `origin/main` avant chaque tour. Le checkout interactif `D:\CoursIA` est souvent sur une branche de travail et ne doit pas executer un organe de branche.

Le porteur est **la tache planifiee qui porte deja `merge_ready`** : `CoursIA\merge_ready`, toutes les 20 minutes (mesure du 2026-10-27 : tics a `:16`, `:36`, `:56`), lanceur masque `%LOCALAPPDATA%\CoursIA\merge_ready\run_hidden.vbs`, journal `%LOCALAPPDATA%\CoursIA\merge_ready\logs\merge_ready_AAAAMMJJ.log`. Forme PowerShell pour ce siege Windows, la variable ne vivant que le temps de la commande :

```powershell
$env:ACTIONS_VARIABLES_PAT = (gh auth token --user jsboige)
python D:\CoursIA-wt-merge-ready\scripts\ci\ci_overflow_controller.py --repo jsboige/CoursIA --apply --json
Remove-Item Env:\ACTIONS_VARIABLES_PAT
```

Le cablage n'est **pas pose dans cette PR** : `scripts/coordination/install_merge_ready_task.py` ne lance aujourd'hui que `merge_ready.py --apply` (sa fonction `task_command`). Attacher la bascule a ce tour est l'ajout d'une commande dans son mode `--run` ; c'est un droit d'ecriture, donc une decision du coordinateur, pas une evidence a prendre dans une PR de controleur.

Ce qui est automatise et public : la **mesure** (file hebergee, inventaire du parc local, etat de la variable), la **decision** (HOLD / `true` / `false`) et l'**ecriture**. Ce qui reste humain et trace : le choix de poser le secret, son perimetre et son expiration.

Le job planifie rend son verdict dans le resume de chaque passage (horaire, minute 31) ; une bascule non effectuee **apparait** dans ce resume, elle n'est jamais silencieuse.

## Mesure de reference (2026-10-27T13:31Z, `origin/main`)

```json
{
  "verdict": "HOLD",
  "reason": "deja a true -- offre hebergee saturee (134 job(s) en file depuis plus de 15 min, plus ancien 74 min) et parc local libre (26 slot(s)) -- le local absorbe",
  "current": "true",
  "written": false,
  "mode": "dry-run",
  "hosted": {"queued": 136, "old": 134, "oldest_age_min": 74.5, "complete": true},
  "local": {"online": 32, "free": 26, "starved": 0, "complete": true}
}
```

Cette mesure est anterieure aux deux corrections de la premise de liberation (« la charge rendue », puis « la charge rendue de la cohorte ») : elle a ete produite par la regle qui lisait la seule file hebergee. Le **verdict** reste identique sous la regle actuelle (la file etait saturee, donc la saturation prime et l'etat etait deja au bout) ; ce qui change est la **premise de liberation**.

Lecture : au moment de la mesure, l'offre hebergee portait **136 jobs en file** (dont 134 de plus de 15 min, le plus ancien a 74 min) pendant que le parc local availait **26 slots libres sur 32 en ligne**. La variable etait deja a `true` : le controleur **n'ecrit rien** (etat deja au bout). C'est cette meme execution qui a servi a compter les 313 appels `gh` ci-dessous.

Le rapport **porte desormais** les etats de troncature des deux lectures (`hosted.truncated`, `local.truncated`, `in_progress_unread`), la **charge rendue de la cohorte** sur ses deux lectures (`cohort`, `cohort_confirm`, avec le compte de workflows derives et le motif de derivation), la **marge hebergee** (`hosted_margin`, `hosted.in_progress`, `thresholds.hosted_cap`) et l'etat du canal d'ecriture (`write_token_env`, `write_token_present`, `write_blocked`, `state_known`, `state_reason`). Le resume du job (`--summary-out`) les restitue en clair, avec une ligne `DEGRADE:` par cause.

## Cout de l'organe (mesure, point 2 de la review ai-01 du 2026-10-27)

**~295 appels `gh` pour une execution.** Mesure du 2026-10-27T18:40Z, compteur pose sur les deux points d'appel de l'organe (`ci_overflow_controller._gh_api` et `check_runner_starvation._gh_json`), sur la file reelle, **budgets 120 / 120** :

| appels | famille |
|---|---|
| 164 | lectures de jobs d'un run (120 heberges + 44 locaux) |
| 125 | re-verification d'un run (residuel « vu au seul listing queued ») |
| 4 | listings de runs (`queued` + `in_progress`, 2 par label) |
| 1 | lecture de la variable de depot |
| 1 | inventaire des runners |

La reference anterieure (**313 appels**, mesure du 2026-10-27T13:31Z) correspondait au **budget local de 40** sur une file plus profonde (160 lectures de jobs). Le passage de 40 a 120 coute **+4 appels** et debloque la lecture locale (44 runs eligibles mesures contre un plafond de 40 : le parc local etait a la limite exacte du budget, donc la troncature y etait une loterie).

Le terme dominant n'est pas le budget de jobs mais la **re-verification du residuel** : chaque entree vue au seul listing `queued` coute une requete `runs/{id}`, et une file hebergee profonde en produit une par job affame (143 pour 136 jobs en file au moment de la mesure de 13:31Z). Ce chiffre n'est pas un plafond theorique, c'est le cout observe d'un passage -- et il **varie avec la profondeur de la file**, pas avec le budget.

**La charge rendue de la cohorte ajoute une troisieme lecture du label local** (vague 3). Elle n'est payee que lorsque la liberation est autrement candidate -- l'offre hebergee n'attend pas et le parc local n'est pas affame -- exactement comme la seconde lecture de confirmation qu'elle remplace ; hors de ce regime, le passage garde le cout ci-dessus. Son volume est borne par `--local-job-budget`, comme la lecture locale, mais le compteur du 27/10 n'a **pas** ete rejoue depuis cet ajout : le surcout n'est pas mesure a ce jour, et il est justifie par le gating, pas par une mesure.

## Cadence et tolerance

Le workflow tourne **une fois par heure, minute 31** (`31 * * * *`) : hors `:00`/`:30` (jitter de la flotte) et distincte des autres crons horaires du depot. Le `23,53` d'origine etait **exactement** le cron de `linux-runner-version-pin-advisory.yml`, que ce dernier avait choisi pour ne pas collisionner (point 3 de la review du 27/10).

Le controleur est desormais inscrit dans le registre de `scripts/ci/check_scheduler_liveness.py`, avec la cadence declaree lue dans ce fichier : un cron qui meurt se **mesure** (`LATE` / `DEAD`), il ne se suppose pas.

L'horaire suffit, et c'est le cout qui le fixe : ~295 appels par passage toutes les 30 minutes feraient environ 14 000 appels par jour pour un organe de controle, exactement ce que le volet 5 de #22937 interdit. A l'inverse, une cadence plus lente ne coute rien en justesse : le controleur est **une machine a etat sur une variable**, un passage tardif agit sur l'etat courant et n'accumule aucun retard. La **livraison** des crons du depot est d'ailleurs tardive et irreguliere (mesure : 22 % des tics horaires servis, mediane 289 min pour une cadence declaree de 60 min sur `pr-gate-stale-sweep` -- cf volet 6 de [#22937](https://github.com/jsboige/CoursIA/issues/22937)).

Le dwell est passe de 30 a **90 min** (point Hermes du 2026-10-27, 12:53Z) : le dwell n'est opposable que s'il **depasse la cadence**, sinon il ne peut jamais bloquer quoi que ce soit. Deux passages consecutifs d'un cron horaire sont a 60 min : un dwell de 30 min etait donc **inerte**, et l'anti-oscillation qu'il pretendait assurer n'existait pas. A 90 min, une bascule peut encore etre revoquee au tic suivant (60 min < 90 min) mais pas au tic d'apres (120 min > 90 min) : l'oscillation rapide est arretee, la machine a etat reste lente. La coherence se **mesure** (`test_dwell_du_controleur_depasse_la_cadence_du_cron`), elle ne se suppose pas.

Le dwell amortit l'oscillation entre deux passages ; il ne cadenche pas, et il ne doit pas faire croire qu'une file revenue a la normale reste gouvernee par une decision d'il y a deux heures.

## Voir aussi

- [#22921](https://github.com/jsboige/CoursIA/pull/22921) — phase A, la forme hybride des 25 workflows ;
- `scripts/ci/check_self_hosted_runner_policy.py` — l'instrument qui enumere les formes de `runs-on` auditees, et l'allowlist fail-closed ou ce workflow doit figurer pour tourner sur le parc local ;
- `scripts/ci/check_scheduler_liveness.py` — le registre de cadence, ou le controleur est desormais inscrit : son extinction se mesure ;
- `scripts/coordination/install_merge_ready_task.py` — la tache `CoursIA\merge_ready`, siege ou la bascule locale a vocation a tourner ;
- `scripts/ci/check_runner_starvation.py` — l'organe de sante du parc, dont le controleur reutilise la mesure de file et l'inventaire des slots ;
- [volet 5 — debit DNS vers api.github.com](https://github.com/jsboige/CoursIA/pull/22948) — l'autre moitie du cout de la CI. Renvoi vers la PR et non vers le fichier : le document `docs/coordination/dns-rate-measurement.md` est livre par cette PR encore ouverte, et un lien fichier casserait `check-links` sur toute branche ne la contenant pas.
