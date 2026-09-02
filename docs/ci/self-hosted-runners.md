# Préparation des runners GitHub Actions auto-hébergés

Cette page décrit les mesures et les garde-fous du chantier #12704. **État au 2026-09-01 : activation partielle sur po-2024, volet Linux conteneurisé en ligne** (2 slots Docker, preuve d'identité `RUNNER_OS = Linux` rendue — cf section Runner Linux conteneurisé ; runner `fast-guards` live, tool-cache seedé, ré-enregistrement sans UAC opérationnel), les autres profils du registre restant en préparation. Le dépôt `jsboige/CoursIA` est public : une PR de fork peut contenir du code non fiable. Toute exécution auto-hébergée reste réservée aux branches du dépôt lui-même, avec une garde YAML explicite en plus des réglages GitHub.

## Mesurer avant de dimensionner

Le collecteur `scripts/ci/measure_runner_demand.py` mesure une cohorte de runs créés dans une fenêtre UTC :

```powershell
python scripts/ci/measure_runner_demand.py `
  --repo jsboige/CoursIA `
  --since 2026-08-24T09:00:00Z `
  --until 2026-08-24T10:00:00Z `
  --output C:/chemin/runner-demand.json
```

La sortie contient le snapshot minimal et son analyse. Elle se rejoue sans accès réseau :

```powershell
python scripts/ci/measure_runner_demand.py `
  --input C:/chemin/runner-demand.json `
  --output C:/chemin/runner-demand-replay.json
```

Les snapshots live datés sont des preuves de session : ils restent hors du dépôt et leurs chiffres, fenêtre et dénominateurs sont cités dans la PR ou sur le dashboard. Le dépôt conserve l'instrument et les définitions durables, pas un rapport d'état.

## Définitions

Pour chaque job disposant de timestamps cohérents :

- **attente** = `started_at - created_at` ;
- **travail runner** = `completed_at - started_at` ;
- **minutes-runner par heure murale** = somme du travail des jobs / durée de la fenêtre ;
- **équivalents runners moyens** = somme du travail / durée de la fenêtre, les deux exprimées en minutes.

`run_started_at` n'est pas utilisé pour l'attente : l'API peut le rendre égal au `created_at` du run alors que ses jobs attendent encore. Un job annulé après avoir démarré a consommé un runner et compte dans le travail. Un job `skipped` ou encore en file ne devient jamais une durée zéro : il apparaît dans `incomplete_or_untimed_jobs` et réduit `timing_coverage`. GitHub peut aussi inverser deux timestamps adjacents d'exactement une seconde à cause de leur précision : ces jobs sont exclus du calcul et comptés dans `timestamp_skew_jobs`; une inversion supérieure à une seconde casse la mesure (`exit 2`).

La provenance est classée en trois catégories :

- `same_repo` : `head_repository.full_name` égale le dépôt mesuré ;
- `fork` : le nom diffère ;
- `unknown` : provenance absente.

Un résultat avec `unknown > 0` ne prouve pas « 100 % same-repo ».

## Exhaustivité et zéros

L'API Actions plafonne certaines recherches filtrées à 1 000 runs. L'instrument bissecte automatiquement la fenêtre temporelle dès que `total_count >= 1000`, déduplique les runs aux frontières, puis pagine tous les jobs de chaque run. Il refuse la mesure (`exit 2`) si une sous-fenêtre d'une seconde reste plafonnée, si une page disparaît avant le dénominateur annoncé ou si des timestamps donnent une durée négative.

Une fenêtre réellement vide est valide et imprime explicitement `runs: 0`, `jobs: 0` et `timing_coverage: null`. Elle est donc distincte d'un instrument cassé. Ne jamais citer un zéro sans son dénominateur et son code retour.

## Lecture de la baseline

Avant toute bascule, relever au minimum :

1. la fenêtre UTC et sa durée ;
2. le nombre de runs, de jobs et de jobs temporisés ;
3. la couverture temporelle ;
4. les minutes-runner/heure ;
5. le détail par workflow et par conclusion ;
6. les comptes `same_repo`, `fork` et `unknown` ;
7. les rafales `runs_created_per_minute`.

Le détail par workflow sépare la capacité réellement consommée de l'auto-contention. En particulier, le `PR gate` peut occuper un runner pendant qu'il sonde des checks eux-mêmes en file : dimensionner sur la demande brute financerait ce temps d'attente au lieu de le corriger.

## Topologie retenue

`jsboige/CoursIA` appartient à un compte GitHub personnel. Les groupes de runners personnalisés sont réservés aux organisations et ne constituent donc pas une barrière disponible ici. La frontière activable repose sur deux contrôles complémentaires :

1. une allowlist statique de workflows ;
2. les labels exacts `self-hosted`, `coursia-ephemeral`, `coursia-fast-guards`.

La capacité est distribuée sur les machines des workers `myia-po-2023` à `myia-po-2026`, pas centralisée sur ai-01. Il n'existe pas d'affinité entre auteur du push et machine d'exécution : GitHub choisit un runner disponible portant les labels. Chaque machine utilise le même compte Windows local dédié et un profil distinct. ai-01 reste hors du pool initial afin de préserver ses charges de coordination, vLLM et entraînement.

Un runner ne doit jamais utiliser un label GitHub-hosted (`ubuntu-latest`, `windows-latest`, etc.) : cela contournerait la classification statique. Il ne doit pas non plus hériter du compte interactif du worker.

## Gestionnaire Windows, à blanc par défaut

Le registre `scripts/ci/self_hosted_runner_profiles.json` épingle pour chaque worker : dépôt, identité locale, chemins possédés, labels, version, URL officielle et SHA-256 du runner. Il ne contient aucun secret.

```powershell
python scripts/ci/manage_self_hosted_runner.py install `
  --profile myia-po-2025-fast-guards
python scripts/ci/manage_self_hosted_runner.py register `
  --profile myia-po-2025-fast-guards
python scripts/ci/manage_self_hosted_runner.py verify `
  --profile myia-po-2025-fast-guards
python scripts/ci/manage_self_hosted_runner.py teardown `
  --profile myia-po-2025-fast-guards
```

Sans `--apply`, ces commandes observent l'état local et impriment un plan JSON déterministe. Elles ne téléchargent rien, ne créent aucun compte, n'écrivent aucun fichier, ne contactent pas GitHub et ne modifient aucun service. Codes retour : `0` plan/état valide, `1` précondition de sécurité refusée, `2` profil ou état illisible.

### Installation ultérieure

`install --apply` est réservé à une session d'activation autorisée et élevée. Il exige `COURSIA_RUNNER_ACCOUNT_PASSWORD` dans l'environnement, puis :

- télécharge uniquement l'archive Windows x64 officielle épinglée ;
- compare son SHA-256 au pin committé avant extraction ;
- refuse les chemins absolus, traversals, symlinks et flux alternatifs NTFS dans le ZIP ;
- extrait dans un staging puis renomme atomiquement ;
- crée un compte local standard dédié et refuse tout compte préexistant/non possédé ;
- retire l'héritage ACL du répertoire runner ;
- ajoute des refus de lecture explicites sur tout le répertoire `.secrets/`, SSH et `GitHub CLI/hosts.yml` ;
- écrit un manifeste local qui borne les ressources que le teardown peut retirer.

Un hash faux, un chemin sensible absent, un compte administrateur ou un état partiel fait échouer l'installation. Aucun fallback vers `LocalSystem`, `NetworkService` ou le compte interactif n'est admis.

### Bouton d'enregistrement — ne pas presser pendant la préparation

`register --apply` est le geste d'activation. Il exige :

- une installation conforme ;
- `GITHUB_RUNNER_REGISTRATION_TOKEN` ;
- `COURSIA_RUNNER_ACCOUNT_PASSWORD`.

Le gestionnaire transmet les secrets via les entrées upstream `ACTIONS_RUNNER_INPUT_*` du runner, et jamais via `--token` ou `--windowslogonpassword` dans la ligne de commande. L'environnement enfant est construit depuis une allowlist et n'hérite ni de `GH_TOKEN`, ni de `GITHUB_TOKEN`, ni du profil interactif. L'invocation fixe `--unattended --ephemeral --replace --runasservice` et les trois labels exacts.

Le token d'enregistrement ne transite jamais par un commit, une PR, un commentaire GitHub ou un dashboard. Le canal éventuel est un DM RooSync privé avec autodestruction adaptée. La commande `register --apply` ne doit être exécutée qu'après un geste explicite du user ou du coordinateur.

### Vérification de l'isolation

Le mode à blanc vérifie manifeste, version, labels et état. `verify --apply`, lors de l'activation contrôlée, exécute sous le compte runner un probe réel qui exige quatre résultats :

1. lecture d'un fichier de contrôle placé dans `.secrets/` refusée ;
2. lecture SSH refusée ;
3. lecture de la configuration/keyring `gh` interactive refusée ;
4. écriture puis suppression dans le workdir réussie.

`whoami` ne suffit pas. Un fichier absent ou une erreur ambiguë n'est jamais assimilé à un refus d'accès réussi. Le probe et son résultat temporaire sont supprimés dans tous les cas.

### Teardown symétrique

`teardown --apply` n'agit que si le manifeste prouve la propriété du chemin et du compte. Pour un runner enregistré, il exige `GITHUB_RUNNER_REMOVAL_TOKEN`, transmis lui aussi par l'environnement upstream. Il arrête et désinstalle le service, désenregistre le runner, copie `_diag` hors workdir, refuse de continuer si un secret fourni apparaît dans les logs, retire les ressources possédées, les ACE et le compte dédié. Un second passage sur un état absent est un succès explicite sans action.

Les logs conservés restent locaux et hors du dépôt. Le contrôle distant « zéro runner enregistré » et la preuve d'un job réel appartiennent à la tranche d'activation, car ils nécessitent l'API GitHub.

## Limite des runners éphémères — et le contrôleur de ré-enregistrement

Un runner `--ephemeral` traite au plus un job puis doit être ré-enregistré : chaque job consomme l'inscription. Le gestionnaire prépare une invocation unique ; il ne crée ni boucle permanente, ni broker de tokens. **La décision est prise** (ai-01, DM 2026-08-28T14:33Z) : un contrôleur de ré-enregistrement supervise l'invocation unique — pas de JIT (il exigerait le broker de tokens que cette page refuse), pas de one-shot (ce n'est pas de la capacité). L'éphémère est préservé : chaque job garde une inscription fraîche, donc un token négocié à chaud à chaque cycle. Un runner persistant n'est pas un raccourci acceptable.

Le contrôleur est `scripts/ci/runner_controller.py` :

| Commande | Effet |
|---|---|
| `status` | État distant + plan, aucun effet de bord. |
| `ensure --apply` | **Idempotent** : runner online → no-op ; absent → token frais via `gh` + `register` + `verify` du gestionnaire. Sans `--apply`, imprime le plan JSON. |
| `deregister --apply` | Arrêt propre : `config.cmd remove` avec token de retrait. L'installation demeure ; l'état redevient « préparé, pas activé ». |
| `task-install --apply` | Enregistre la tâche planifiée `CoursIA-Runner-Controller` (tick 60 s, limite d'exécution 10 min, `IgnoreNew`) qui déclenche `ensure --apply`. **C'est le bouton** — exige une session élevée. |
| `task-remove --apply` | Retire la tâche (retour arrière du bouton). Second passage sur une tâche absente = succès explicite. |

Le tick ne fait quasiment rien quand le runner est online (une lecture d'API) : autant de passages que de minutes, un seul état stable. L'action de la tâche lit le mot de passe du compte dédié dans le fichier machine local conventionnel (`<racine-parent>\secrets\runner_pwd.txt`, jamais dans le dépôt), négocie tout le reste à chaud et journalise dans `<racine-parent>\logs\controller.log`. Le token d'enregistrement ne transite jamais par argv, commit, PR, commentaire ou dashboard, et est retiré de l'environnement après chaque cycle.

**Geste d'activation** (ai-01 ou user, session élevée) : `python scripts/ci/runner_controller.py task-install --profile <profil> --apply`, puis observer `logs\controller.log` et `gh api repos/jsboige/CoursIA/actions/runners`.

**Geste de retour arrière** : `task-remove --apply` (la machine cesse de ré-enregistrer), puis laisser le job courant consommer l'inscription — ou `deregister --apply` pour l'arrêt immédiat. Le teardown complet du gestionnaire (compte, ACL, arborescence) reste disponible en dernier recours.

**Nom de route (2026-08-28, mesuré firsthand sous `myia-ai-01`)** : la route de retrait est `POST /actions/runners/remove-token`, **pas** `removal-token`. Les trois mesures sous une même identité non-admin lèvent l'ambiguïté : `registration-token` → **403**, `remove-token` → **403** (la route existe, seul le droit manque), `removal-token` → **404** (la route n'existe pas). Il n'y a donc **aucune asymétrie d'API** entre l'enregistrement et le retrait — le 404 initialement observé venait du nom de route erroné, corrigé ici. L'élévation reste requise pour l'appel réel (201 sous identité admin, cf. `registration-token` mesuré par po-2024) : `deregister --apply` échoue fail-closed sous identité non-admin, ce qui est le comportement voulu.

## Provisionnement Python du tool-cache (option a2)

`windows-self-hosted-tests.yml` conserve `actions/setup-python`. Les deux alternatives ont été écartées sur preuve (arbitrage #13217, 2026-08-27) :

- **Python machine sans `setup-python`** (PR #13233, fermée) : le compte dédié `.\coursia-runner` n'a aucun `python` dans son PATH — les installations per-user de `C:\Users\<worker>\AppData\Local\Programs\Python` sont hors PATH système et hors ACL du compte service. Mesuré au run 33087876304 : « The term 'python' is not recognized » (`Install test dependencies`, 2 s).
- **Install all-users + PATH** (option a1) : fonctionnelle mais exige une passe UAC ; non retenue tant que l'alternative sans UAC existe.

Sur un runner éphémère sans provisionnement, le premier `setup-python` télécharge l'interpréteur et son `setup.ps1` est bloqué par l'ExecutionPolicy du compte service (défaut fondateur de #13217). La voie retenue, déployée et mesurée sur po-2024 : **seeder le tool-cache du runner avec un Python épinglé et son stamp de complétude**, pour que `setup-python` trouve l'interpréteur en cache local et n'exécute jamais `setup.ps1` — zéro téléchargement, zéro script d'installation.

### Le stamp est la pièce critique

Un seed sans stamp échoue en détruisant le seed. Sans fichier `x64.complete`, `tc.find()` répond « was not found in the local cache » ; `setup-python` télécharge, et son `setup.ps1` **trouve le dossier seedé, le supprime, puis copie uniquement l'installeur** — l'archive `actions/python-versions` embarque un exécutable, pas un arbre — et échoue en l'exécutant sous le compte service (`0x80070005`, reproduit hors job). Avec le stamp : cache hit immédiat.

### Procédure (mesurée sur po-2024)

1. Installer Python 3.11.9 **per-user** (python.org, hors UAC) sur le compte interactif du worker.
2. Peupler le tool-cache par `robocopy` vers `<work>\_tool\Python\3.11.9\x64\` sous le compte `.\coursia-runner` (2820 fichiers) — si le compte interactif peut écrire sous `_work\_tool` (ACL par profil), le robocopy direct suffit ; sinon l'exécuter as `coursia-runner`.
3. Écrire le stamp vide `<work>\_tool\Python\3.11.9\x64.complete` — **frère** du répertoire `x64\`, jamais dedans. `@actions/tool-cache` compose `<cache>/<tool>/<version>/<arch>` puis teste ce **même** chemin suffixé de `.complete` : `find()` évalue `fs.existsSync(cachePath) && fs.existsSync(cachePath + '.complete')`, et `_completeToolPath()` écrit `markerPath = folderPath + '.complete'`. Un marqueur placé *dans* `x64\` n'est donc jamais lu — `tc.find()` répond « not found », et le seed est détruit au premier job par le `io.rmRF(folderPath)` de `_createToolPath()`.
4. Vérifier sous le compte service : `python --version` → `3.11.9` et `pip --version` → 24.0 (le témoin `TOOL_PYOK 3.11.9` des runs de preuve).

Le tool-cache et le stamp persistent sous `_work` entre jobs éphémères : les ré-enregistrements suivants gardent le cache hit.

### Preuves mesurées (po-2024, 2026-08-27)

- run 33092567324 (main, 16:19Z) : `setup-python` **success** (cache hit), pip success, pytest 39 passed / 1 failed — l'échec résiduel était le bug d'invariant #13238, sans rapport avec le provisionnement ;
- run 33093119578 (branche, 16:25Z) : **42 passed**, conclusion success ;
- run de contrôle sans stamp : `0x80070005`, le dossier seedé détruit par `setup.ps1` (mécanisme ci-dessus).

### Ré-enregistrement sans UAC (chaîne po-2024)

Chaque `workflow_dispatch` consomme l'enregistrement éphémère (un job, un runner) : la chaîne de ré-enregistrement doit donc tourner sans intervention élevée. Mise au point sur po-2024 (2026-08-27) :

- **tâche planifiée `CoursIA-Runner-Activate`** : exécute périodiquement le `register --apply` du gestionnaire (les secrets d'enregistrement restent transmis par l'environnement upstream, jamais en ligne de commande) ;
- **listener interactif lancé sous le compte dédié** : le service runner démarre dans la session du compte `.\coursia-runner`, sans élévation ;
- résultat mesuré : dispatch 16:00Z pris par un runner ré-enregistré automatiquement — « la machinery vit » sans passe UAC par cycle.

Le stamp `_work\_tool` (section précédente) persiste à travers ces cycles : le cache hit survit aux ré-enregistrements.

Diagnostic complet et arbitrage : #13217. Chantier runners : #12704.

## Runner Linux conteneurisé (po-2024, mission #13378)

Le volet Linux du chantier passe par **Docker plutôt que WSL nu** (décision user relayée par ai-01, dispatch 2026-08-31) : isolation (conteneur jetable vs compte Windows sous ACL), éphémérité native (cycle de vie porté par `docker run --rm`, pas de ré-enregistrement à orchestrer côté service), plafonnement ressources par le daemon.

**Contexte** : `scripts/ci/docker/linux-runner/` (Dockerfile — runner 2.336.0 linux-x64 épinglé par SHA-256 officiel, utilisateur non-root, aucun montage hôte ; entrypoint — enregistrement via `ACTIONS_RUNNER_INPUT_*` uniquement, jamais `--token` en argv).

**Lancement cappé** (contraintes user : la machine sert aussi de workstation GPU + interactive — l'hôte prime sur la CI) :

```bash
TOKEN=$(gh api repos/jsboige/CoursIA/actions/runners/registration-token --jq .token)
docker run --rm -d --name coursia-linux-runner \
  --cpus=3 --memory=4g --pids-limit=384 \
  --security-opt=no-new-privileges \
  -e ACTIONS_RUNNER_INPUT_TOKEN="$TOKEN" \
  -e ACTIONS_RUNNER_INPUT_URL=https://github.com/jsboige/CoursIA \
  -e ACTIONS_RUNNER_INPUT_NAME=myia-po-2024-linux-docker \
  -e ACTIONS_RUNNER_INPUT_LABELS=self-hosted,coursia-ephemeral,coursia-linux \
  coursia-linux-runner:2.336.0
```

Pas de `--gpus` (aucun passthrough GPU, par design). Le runner `--ephemeral` traite **au plus un job** puis se désenregistre et le conteneur `--rm` disparaît : un dispatch = un job = un conteneur.

**Ce cycle mono-job est le facteur limitant nommé par le census #13378** — pas la compatibilité des workflows. Un `docker run` isolé plafonne donc la concurrence à 1, ce qui ne débraye rien : c'est le superviseur ci-dessous qui lève ce plafond.

### Superviseur — le plafond de 1 job se lève par N boucles

`scripts/ci/docker/linux-runner/supervise.sh` (livré 2026-09-01, finalisation du volet laissé en conception). Un slot = une boucle `while` qui relance un conteneur dès que le précédent meurt ; **N slots = N jobs concurrents**. C'est toute la différence entre le conteneur et le service Windows : côté Windows, chaque ré-enregistrement est une tâche planifiée à orchestrer ; ici c'est un `docker run` de plus, gratuit et parallélisable.

```bash
docker build -t coursia-linux-runner:2.336.0 scripts/ci/docker/linux-runner/
scripts/ci/docker/linux-runner/supervise.sh start 2   # 2 slots concurrents
scripts/ci/docker/linux-runner/supervise.sh status
scripts/ci/docker/linux-runner/supervise.sh stop      # gracieux : les jobs en cours finissent
```

Trois points de conception qui ne sont pas négociables :

- **La boucle vit sur l'hôte, jamais dans l'image.** Le `registration token` vaut 1 h et est jetable : il en faut un neuf à chaque démarrage de conteneur. Le fetch exige `gh` authentifié avec droit admin sur le dépôt — ces credentials ne descendent jamais dans le conteneur, qui ne reçoit que le token par `-e`, comme l'exige déjà `entrypoint.sh`.
- **L'arrêt est gracieux par défaut** (sentinel `~/.coursia-runner/stop`) : plus aucun conteneur n'est lancé, mais le job en cours va à son terme. Tuer un job en vol produirait un rouge qui ne veut rien dire.
- **N appartient à po-2024, pas à ai-01.** Le défaut est 2, volontairement bas. La clause de souveraineté ci-dessous prime sur toute décision d'élargissement.

**Labels dédiés** : le jeu `{self-hosted, coursia-ephemeral, coursia-linux}` (second jeu admis par `check_self_hosted_runner_policy.py`) route uniquement vers le conteneur — un dispatch Windows ne peut jamais y atterrir, un job Linux ne peut jamais atterrir sur un runner Windows. Mélanger les deux jeux reste une violation (`RUNNER_LABELS`).

**État déployé le 2026-09-01 (po-2024, inventaire GitHub firsthand ~20:27Z)** : 2 slots `myia-po-2024-linux-docker-1/-2` `[online]`, labels `{self-hosted, coursia-ephemeral, coursia-linux}`, image 2.336.0, lancés par `supervise.sh start 2`. **Preuve d'identité rendue** : run 33554804211 — `Runner name: 'myia-po-2024-linux-docker-1'`, `runner.os=Linux`, job 1 m 51 s, conclusion success. Empreinte au repos mesurée sur les deux conteneurs : ~40,5 MiB / 4 GiB chacun, CPU ~0 %, PIDS 14-18. **Empreinte sous charge** (deux jobs organiques concurrents, ~21:55Z) : CPU 113 % et 161 % (cap 300 %), MEM 187 MiB et 498 MiB (cap 4 GiB), PIDS 52 et 50 (cap 384) — la jambe tient N=2 concurrent sans approcher les caps. La boucle de supervision est prouvée : après la mort éphémère du conteneur post-job, ré-enregistrement automatique observé et runners repassés `[online]`.

La leçon qui a fondé cette preuve reste écrite noir sur blanc : cette page a déjà décrit une conception comme un état déployé — l'inventaire du matin même (2026-09-01) montrait un registre à **un seul** runner Windows, label `coursia-linux` orphelin nulle part, image jamais construite. Tant qu'aucun job n'a rendu la preuve d'identité (`RUNNER_OS = Linux` dans les logs), aucun vert de cette chaîne ne prouve quoi que ce soit — leçon po-2024 du run 33178577527, où l'échec s'était produit *pour la mauvaise raison* (ACE manquante) et aurait pu passer pour un succès de routage.

L'image expose `python` nu (`python-is-python3`) pour les workflows stdlib-only (le `check-navlinks` du job 100021313259 avait échoué `exit 127 "python: not found"` avant cela), et les slots montent le volume `coursia-runner-toolcache` sur `/opt/hostedtoolcache` (`RUNNER_TOOL_CACHE`) pour que les actions `setup-*` ne re-téléchargent pas leurs outils à chaque conteneur éphémère. Après toute modification du Dockerfile : rebuild (même tag), puis roulement des slots — `docker kill` des conteneurs vérifiés `busy=false` (la boucle relance sur la nouvelle image ; les slots occupés se soignent seuls au tour suivant). **Le check `busy=false` échoue en silence par deux chemins mesurés** : `jq` est absent de l'hôte Ubuntu (il vit dans l'image), et `gh api` ne supporte pas `--arg`. Forme canonique — côté Windows (gh embarque jq), nom littéral interpolé, **fail-closed** :

```bash
busy=$(gh api repos/jsboige/CoursIA/actions/runners --jq ".runners[] | select(.name==\"$name\") | .busy")
rc=$?; [ $rc -eq 0 ] && [ -n "$busy" ] || { echo "check FAILED rc=$rc busy='$busy'"; exit 1; }
```

Re-vérifier **par slot juste avant chaque kill** : un job peut être pris entre l'inventaire et le geste. Un `busy` vide capturé sans contrôle de `rc` n'est pas une vérification — l'égalité `!= "true"` passe et le kill part non vérifié.

**Cache de dépôt persistant (#14285, 2026-09-02)** : chaque slot monte en plus un volume dédié `coursia-runner-work-<slot>` sur `/home/runner/_work`. Sans lui, `--rm` détruisait le clone avec le conteneur et `actions/checkout` re-clonait le dépôt **entier à chaque job** — mesure #14285 : checkout 80-148 s (contre 40-51 s sur `ubuntu-latest`), ~97 % du temps du job, pour un pack de 3,54 GiB. Avec le volume, checkout trouve un clone existant et fait un `git fetch` incrémental ; son `clean` par défaut nettoie l'arbre entre jobs. Un volume **par slot** (jamais partagé : deux jobs concurrents se battraient sur le même `.git`), ~4 GiB par slot sur le disque hôte. **Contrôle d'acceptance** : le premier job après création du volume paie encore le clone complet (attendu) ; si le **second** job paie le même prix, le volume n'est pas pris en compte et le correctif est inerte. **Garde liée** : la persistance de `_work` n'est sûre que tant qu'aucun code de fork n'atteint ces runners (~95 forks étudiants) — si la garde fork saute, ce volume devient un vecteur inter-jobs et la persistance doit être retirée **avant** d'ouvrir un trigger `pull_request`.

Routage (décision coordinateur) — **tranche 1 portée par #14148 (PR ouverte au 2026-09-01)** : 11 workflows y passent sur les labels `coursia-linux`, sous la règle « allowlist du checker `check_self_hosted_runner_policy.py` + garde universelle de fork/payload + timeout + `permissions: read` ». Tant qu'elle n'est pas mergée, ces workflows restent sur GitHub-hosted. Le reste des 93 jobs `ubuntu-latest` du census #13378 demeure sur GitHub-hosted tant que l'empreinte n'a pas été mesurée sur des jobs réels — l'élargissement (tranche 2, N slots) reste décision coordinateur après 24 h de vert sur la tranche 1.

**Le gestionnaire ne bloque pas.** `manage_self_hosted_runner.py` et `self_hosted_runner_profiles.json` sont Windows-only *par validation* (« must pin an official Windows x64 archive ») : ils ne peuvent pas porter un profil Linux aujourd'hui. Ce n'est pas un blocage — `supervise.sh` fonctionne sans eux, sans aucune PR préalable. Étendre le gestionnaire aux profils Linux est une **PR de suivi**, jamais la condition du débrayage.

Si l'empreinte mesurée pendant un job gêne la workstation (training GPU, sessions interactives), on **réduit les caps ou on arrête**, et on le signale à ai-01.

### Persistance du superviseur — déployée sur po-2024 (systemd dans Ubuntu + holder WSL)

`supervise.sh` vit dans une session : si elle meurt, les slots en ligne consomment leur inscription au prochain job et rien ne les relance. Le déploiement durable est **posé et mesuré sur po-2024** (2026-09-02, mandat user « Il faut du persistant !!! ») : les slots ont quitté Docker Desktop pour la distro **Ubuntu sous systemd**, et le réveil de la distro est **tenu** par un processus holder Windows. Copies de référence committées dans `scripts/ci/docker/linux-runner/persist/`.

**Architecture (3 étages)** :

1. **Étage Linux (systemd)** — la distro Ubuntu tourne avec systemd en PID 1. `docker-ce` (pas Docker Desktop) est épinglé sur `/var/run/docker-ce.sock` via un drop-in `docker.service.d/coursia-socket.conf`. L'unité système `coursia-runner.service` (`Requires=docker.service`, `Restart=always`, `TimeoutStopSec=900`) exécute le wrapper `/usr/local/bin/coursia-runner-start.sh start 4` : il relit le token admin GitHub à **chaque invocation** depuis `master.env` côté Windows (`/mnt/c/...` via `sed` + `tr -d '\r'` — un CRLF tuerait la valeur ; le token ne vit jamais dans la distro ni dans un argv), exporte `DOCKER_HOST`/`GH_TOKEN`/`COURSIA_RUNNER_STATE_DIR=/var/lib/coursia-runner`, puis `exec supervise.sh start N`. `ExecStop` passe par l'arrêt gracieux (sentinel) : un job en vol va à son terme.
2. **Étage pont (tâche planifiée)** — `CoursIA-LinuxRunners` (`InteractiveToken`, `LeastPrivilege`, logon) exécute `launch-runner.sh` : il ne fait rien lui-même, il invoque le holder et rend son rc.
3. **Étage holder (la pièce non négociable)** — `hold-runner.ps1` spawn un processus `wsl.exe` **détaché** qui exécute `systemctl start coursia-runner.service && exec sleep infinity`. Tant que ce processus vit, une session client WSL existe et **la distro ne peut pas être reapée**.

**Pourquoi le holder est obligatoire — mesure décisive du 2026-09-02** : un appel `wsl.exe` one-shot ne suffit **jamais**. Séquence mesurée : 4 slots `[online]` → sortie du dernier client wsl → **moins de 3 minutes plus tard, distro morte** (`wsl -l --running` : Ubuntu absente ; GitHub : `online: 0`) — avec systemd en PID 1, le service actif et les conteneurs lancés. WSL reape la distro au départ du dernier client, quel que soit son état interne. Ce constat **unifie** tous les échecs de réveil one-shot observés : le pont logon qui « rend rc=0 » sans jamais remonter les slots, et la tâche S4U d'un autre hôte « rc=0 sans rien démarrer » — le rc=0 dit que la demande a été acceptée, pas que la distro a survécu au client. `wsl -l --running` (listage pur, qui ne réveille pas les distros) est le seul instrument de liveness qui ne confonde pas la mesure.

**Mesures d'appoint** :

- **Guerre de flap name-replace** : enregistrer un runner sous un nom existant **remplace** l'entrée (« Successfully replaced the runner »). Deux superviseurs sur les mêmes noms → boucle auto-entretenue `Error: Conflict / Retrying until reconnected` (cadence ~2 min < TTL session ~3 min : ça ne converge jamais). Correctif mesuré : arrêt complet **~5 min** (purger TOUTES les sessions), puis start unique → 4/4 online en 20 s. Corollaire : la bascule Docker Desktop → Ubuntu **remplace** les entrées, elle ne les duplique pas.
- **S4U exige l'élévation** : `Register-ScheduledTask -LogonType S4U` est refusé sans admin (« Accès refusé », même `RunLevel Limited`). La tâche boot `CoursIA-LinuxRunners-Boot` (S4U + `AtStartup`, script prêt) attend **un clic UAC** du user — le pont logon couvre le cas nominal en attendant. Limite connue du pont `InteractiveToken` : le holder meurt à la fermeture de session ; la tâche S4U boot la relance avant le logon.

**Recette de réplication** (un autre worker) : installer docker-ce dans la distro + drop-in socket → poser le wrapper et l'unité (`persist/coursia-runner-start.sh`, `persist/coursia-runner.service`, en adaptant `NAME_PREFIX` et N) → `systemctl enable --now coursia-runner` → créer la tâche logon qui appelle `persist/launch-runner.sh` (elle appelle le holder local) → valider par le protocole de mesure ci-dessus (tuer la distro, déclencher la tâche, **attendre 3+ min sans aucun appel wsl**, puis lister). L'installation d'un mécanisme permanent d'enregistrement reste un geste explicite (coordinateur ou user), jamais silencieux.

## Tranches suivantes, activation partielle

La préparation complète reste découpée :

1. **Mesure** — instrument de cette page.
2. **Isolation statique** — scanner fail-closed, allowlist et labels dépôt.
3. **Cycle de vie local** — gestionnaire, profils, probes et teardown décrits ci-dessus.
4. **Commutation** — un seul point de bascule et garde **universelle** de fork/payload sur chaque workflow routé : `github.event.pull_request.head.repo.full_name == github.repository` ; aucun `pull_request_target` auto-hébergé. C'est la forme appliquée par #14148 aux 11 workflows de la tranche 1.
5. **Preuve contrôlée** — autorisation explicite, une exécution légère réussie, contrôle négatif fork/payload (livré : garde #13387, simulation run 33185586681), puis teardown et preuve que l'état initial est restauré.
6. **Capacité** — le contrôleur ci-dessus ; son test de bout en bout (tâche posée → tick → job consommé → ré-enregistrement observé → tâche retirée) exige une session élevée : c'est la checklist de la session d'activation, le bouton appartient au coordinateur ou au user.

État au 2026-08-28 : les tranches 1-3 sont livrées ; la tranche 4 est active sur po-2024 (jobs réels consommés par le pool `coursia-fast-guards`, ex. runs 33092567324 et 33093119578) ; la preuve contrôlée complète (5) et l'extension du pool aux autres machines restent à faire. Chaque extension machine exige le provisionnement Python de la section dédiée avant le premier job.

| Profil du registre | État — inventaire GitHub firsthand du 2026-09-01 |
|---|---|
| `myia-po-2023-fast-guards` | en préparation (aucun runner enregistré) |
| `myia-po-2024-fast-guards` | **actif** — seul runner du dépôt ; Windows ; tool-cache seedé (a2), ré-enregistrement sans UAC, jobs réels consommés |
| `myia-po-2025-fast-guards` | en préparation (aucun runner enregistré) |
| `myia-po-2026-fast-guards` | en préparation (aucun runner enregistré ; profil vérifié dans le registre) |
| `coursia-linux` (conteneur) | **en ligne + persistant** — 4 slots conteneurisés sur po-2024 (`myia-po-2024-linux-docker-1..4`) sous systemd dans Ubuntu (holder WSL, cf section Persistance), preuve d'identité run 33554804211 (`RUNNER_OS = Linux`) |

La colonne est datée d'une **mesure**, pas d'une intention : le tableau précédent portait « actif » et « en préparation » sans dire ce qui avait été compté, ce qui a laissé lire une conception comme un déploiement.

Le réglage GitHub « Require approval for all outside collaborators » complète la garde YAML ; il ne la remplace jamais (non exposé par l'API `/actions/permissions` — capture à faire côté admin, UI Settings → Actions). L'activation finale reste un geste explicite du user ou du coordinateur, après validation des tranches précédentes.
