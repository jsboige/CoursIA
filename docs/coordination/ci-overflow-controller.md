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

Un **dwell** de `--dwell-minutes` (30 par defaut) interdit deux bascules rapprochees : une variable qui oscille est pire qu'une variable stable.

L'organe est **fail-CLOSED** : une mesure illisible (listing incomplet, inventaire des runners inaccessible) ne produit **aucune** ecriture.

## Usage

```bash
# verdict seul (defaut : dry-run, aucune ecriture)
python scripts/ci/ci_overflow_controller.py --repo jsboige/CoursIA --json

# application effective
python scripts/ci/ci_overflow_controller.py --repo jsboige/CoursIA --apply --json
```

Codes de retour : `0` nominal (HOLD ou bascule), `1` mesure illisible (`UNREADABLE`), `2` refus (`REFUSED` : jeton absent ou droit insuffisant).

## Qui ecrit — arbitrage (b) du coordinateur (c.6441695482, 27/10)

**Le workflow automatise ne bascule rien : il rend un verdict, en lecture seule.** Aucun secret `ACTIONS_VARIABLES_PAT` n'est pose dans Actions, et la portee `variables` **n'existe pas** dans la liste des portees admises sous `permissions:` (reference de syntaxe des workflows GitHub : actions, attestations, checks, contents, deployments, discussions, id-token, issues, packages, pages, pull-requests, security-events, statuses). Une cle hors liste rend le fichier entier invalide : la porter ici aurait suffi a empecher le workflow de demarrer. Les portees du job sont donc `actions: read` + `contents: read`, et la seule voie qui pourrait ecrire reste un jeton a effet de bord dans le depot, refusee par l'arbitrage.

Corollaire mesure a la source, pas suppose : **le verdict suppose que le jeton du run puisse LIRE la variable** (endpoint `actions/variables`). Si ce droit manque, l'organe rend `REFUSED` (code 2) et n'ecrit rien ; le job reste vert -- advisory par construction -- mais son resume porte le verdict `REFUSED` et un `::warning::` nomme le code retour. Ce point se verifie au **premier passage reel** du workflow, pas par lecture du code.

La **bascule** est un geste d'operateur, joue par **ai-01** en local, avec le jeton `jsboige` **pris commande par commande** :

```bash
GH_TOKEN=$(gh auth token --user jsboige) \
  python scripts/ci/ci_overflow_controller.py --repo jsboige/CoursIA --apply --json
```

### Ou cette commande tourne (point 2 de la review ai-01 du 2026-10-27)

Sur le **siege du coordinateur, `D:\CoursIA-wt-merge-ready`** : un worktree detache, ramene sur `origin/main` avant chaque tour. Le checkout interactif `D:\CoursIA` est souvent sur une branche de travail et ne doit pas executer un organe de branche.

Le porteur est **la tache planifiee qui porte deja `merge_ready`** : `CoursIA\merge_ready`, toutes les 20 minutes (mesure du 2026-10-27 : tics a `:16`, `:36`, `:56`), lanceur masque `%LOCALAPPDATA%\CoursIA\merge_ready\run_hidden.vbs`, journal `%LOCALAPPDATA%\CoursIA\merge_ready\logs\merge_ready_AAAAMMJJ.log`. Forme PowerShell pour ce siege Windows, la variable ne vivant que le temps de la commande :

```powershell
$env:GH_TOKEN = (gh auth token --user jsboige)
python D:\CoursIA-wt-merge-ready\scripts\ci\ci_overflow_controller.py --repo jsboige/CoursIA --apply --json
Remove-Item Env:\GH_TOKEN
```

Le cablage n'est **pas pose dans cette PR** : `scripts/coordination/install_merge_ready_task.py` ne lance aujourd'hui que `merge_ready.py --apply` (sa fonction `task_command`). Attacher la bascule a ce tour est l'ajout d'une commande dans son mode `--run` ; c'est un droit d'ecriture, donc une decision du coordinateur, pas une evidence a prendre dans une PR de controleur.

Ce qui est automatise et public : la **mesure** (file hebergee, inventaire du parc local, etat de la variable) et la **decision** (HOLD / `true` / `false`). Ce qui reste humain et trace : l'ecriture.

Le job planifie rend donc son verdict dans le resume de chaque passage (horaire, minute 31) ; une bascule non effectuee **apparait** dans ce resume, elle n'est jamais silencieuse.

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

## Cout de l'organe (mesure, point 2 de la review ai-01 du 2026-10-27)

**313 appels `gh` pour une execution.** Mesure du 2026-10-27T13:31Z, compteur pose sur les deux points d'appel de l'organe (`ci_overflow_controller._gh_api` et `check_runner_starvation._gh_json`), execution en `--json` sans `--apply` (lecture seule), sur la file reelle :

| appels | famille |
|---|---|
| 160 | lectures de jobs d'un run (budget sature : 120 heberges + 40 locaux) |
| 143 | re-verification d'un run (residuel « vu au seul listing queued ») |
| 8 | listings de runs (`queued` + `in_progress`) |
| 1 | lecture de la variable de depot |
| 1 | inventaire des runners |

Le terme dominant n'est pas le budget de jobs mais la **re-verification du residuel** : chaque entree vue au seul listing `queued` coute une requete `runs/{id}`, et une file hebergee profonde en produit une par job affame (143 pour 136 jobs en file au moment de la mesure). Ce chiffre n'est pas un plafond theorique, c'est le cout observe d'un passage.

## Cadence et tolerance

Le workflow tourne **une fois par heure, minute 31** (`31 * * * *`) : hors `:00`/`:30` (jitter de la flotte) et distincte des autres crons horaires du depot. Le `23,53` d'origine etait **exactement** le cron de `linux-runner-version-pin-advisory.yml`, que ce dernier avait choisi pour ne pas collisionner (point 3 de la review du 27/10).

Le controleur est desormais inscrit dans le registre de `scripts/ci/check_scheduler_liveness.py`, avec la cadence declaree lue dans ce fichier : un cron qui meurt se **mesure** (`LATE` / `DEAD`), il ne se suppose pas.

L'horaire suffit, et c'est le cout qui le fixe : 313 appels par passage toutes les 30 minutes feraient environ 15 000 appels par jour pour un organe de controle, exactement ce que le volet 5 de #22937 interdit. A l'inverse, une cadence plus lente ne coute rien en justesse : le controleur est **une machine a etat sur une variable**, un passage tardif agit sur l'etat courant et n'accumule aucun retard. La **livraison** des crons du depot est d'ailleurs tardive et irreguliere (mesure : 22 % des tics horaires servis, mediane 289 min pour une cadence declaree de 60 min sur `pr-gate-stale-sweep` -- cf volet 6 de [#22937](https://github.com/jsboige/CoursIA/issues/22937)).

Le dwell de 30 min reste celui de l'organe. Il est plus court que l'intervalle d'une heure, donc il n'interdit pas la bascule inverse au tic suivant : c'est le sens voulu. Le dwell amortit l'oscillation entre deux passages ; il ne cadenche pas, et il ne doit pas faire croire qu'une file revenue a la normale reste gouvernee par une decision d'il y a deux heures.

## Voir aussi

- [#22921](https://github.com/jsboige/CoursIA/pull/22921) — phase A, la forme hybride des 25 workflows ;
- `scripts/ci/check_self_hosted_runner_policy.py` — l'instrument qui enumere les formes de `runs-on` auditees, et l'allowlist fail-closed ou ce workflow doit figurer pour tourner sur le parc local ;
- `scripts/ci/check_scheduler_liveness.py` — le registre de cadence, ou le controleur est desormais inscrit : son extinction se mesure ;
- `scripts/coordination/install_merge_ready_task.py` — la tache `CoursIA\merge_ready`, siege ou la bascule locale a vocation a tourner ;
- `scripts/ci/check_runner_starvation.py` — l'organe de sante du parc, dont le controleur reutilise la mesure de file et l'inventaire des slots ;
- [volet 5 — debit DNS vers api.github.com](dns-rate-measurement.md) — l'autre moitie du cout de la CI.
