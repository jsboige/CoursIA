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
| file hebergee **videe** (au plus `--drain-jobs` job en file) | variable a `false` |
| parc local **lui-meme affame** (des jobs `coursia-linux` attendent) | variable a `false` (on rend la main a l'heberge) |
| sinon | **HOLD** (rien n'est ecrit) |

Un **dwell** de `--dwell-minutes` (90 par defaut) interdit deux bascules rapprochees : une variable qui oscille est pire qu'une variable stable. Le dwell est **coherent avec la cadence** : il la depasse (90 > 60 min), sinon il ne peut jamais opposer quoi que ce soit -- deux passages consecutifs d'un cron horaire sont toujours a plus de 60 min, et un dwell de 30 min etait donc inerte (point Hermes du 2026-10-27, 12:53Z).

L'organe est **fail-CLOSED** : une mesure illisible (listing incomplet, inventaire des runners inaccessible) ne produit **aucune** ecriture.

Une lecture **tronquee** (budget de lecture atteint) n'est pas une mesure illisible : c'est une mesure **partielle**, dont les comptes sont des bornes **inferieures**. La regle appliquee est **directionnelle** -- une borne inferieure etablit une affirmation **positive** (« au moins N jobs ages ») mais **n'etablit aucune affirmation negative** (« aucun job en file », « le parc local n'est pas affame ») :

| lecture tronquee | conclusion bloquee | conclusion conservee |
|---|---|---|
| offre hebergee | « la file hebergee est **videe** » -> pas de bascule vers `false` | « l'offre hebergee est **saturee** » -> la bascule vers `true` reste possible |
| parc local | « le parc local **n'est pas affame** » -> pas de bascule vers `true` | « le parc local **est affame** » -> la bascule vers `false` reste possible |

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

Lecture : au moment de la mesure, l'offre hebergee portait **136 jobs en file** (dont 134 de plus de 15 min, le plus ancien a 74 min) pendant que le parc local availait **26 slots libres sur 32 en ligne**. La variable etait deja a `true` : le controleur **n'ecrit rien** (etat deja au bout). C'est cette meme execution qui a servi a compter les 313 appels `gh` ci-dessous.

Le rapport **porte desormais** les etats de troncature des deux lectures (`hosted.truncated`, `local.truncated`, `in_progress_unread`) et l'etat du canal d'ecriture (`write_token_env`, `write_token_present`, `write_blocked`, `state_known`, `state_reason`). Le resume du job (`--summary-out`) les restitue en clair, avec une ligne `DEGRADE:` par cause.

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
