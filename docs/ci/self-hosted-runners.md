# Préparation des runners GitHub Actions auto-hébergés

Cette page décrit les mesures et les garde-fous du chantier #12704. **État au 2026-08-28 : activation partielle sur po-2024** (runner `fast-guards` live, tool-cache seedé — cf section Provisionnement ; ré-enregistrement sans UAC opérationnel), les autres profils du registre restant en préparation. Le dépôt `jsboige/CoursIA` est public : une PR de fork peut contenir du code non fiable. Toute exécution auto-hébergée reste réservée aux branches du dépôt lui-même, avec une garde YAML explicite en plus des réglages GitHub.

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

## Limite des runners éphémères

Un runner `--ephemeral` traite au plus un job puis doit être ré-enregistré. Le gestionnaire prépare une invocation unique ; il ne crée ni boucle permanente, ni broker de tokens. Le choix entre configuration JIT, contrôleur de ré-enregistrement ou preuve one-shot est une décision séparée avant activation durable. Un runner persistant n'est pas un raccourci acceptable.

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
3. Écrire le stamp vide `<work>\_tool\Python\3.11.9\x64\x64.complete`.
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

## Tranches suivantes, activation partielle

La préparation complète reste découpée :

1. **Mesure** — instrument de cette page.
2. **Isolation statique** — scanner fail-closed, allowlist et labels dépôt.
3. **Cycle de vie local** — gestionnaire, profils, probes et teardown décrits ci-dessus.
4. **Commutation** — un seul point de bascule et garde `github.event.pull_request.head.repo.full_name == github.repository`; aucun `pull_request_target` auto-hébergé.
5. **Preuve contrôlée** — autorisation explicite, une exécution légère réussie, contrôle négatif fork/payload, puis teardown et preuve que l'état initial est restauré.

État au 2026-08-28 : les tranches 1-3 sont livrées ; la tranche 4 est active sur po-2024 (jobs réels consommés par le pool `coursia-fast-guards`, ex. runs 33092567324 et 33093119578) ; la preuve contrôlée complète (5) et l'extension du pool aux autres machines restent à faire. Chaque extension machine exige le provisionnement Python de la section dédiée avant le premier job.

| Profil du registre | État au 2026-08-28 |
|---|---|
| `myia-po-2023-fast-guards` | en préparation (pas de runner installé) |
| `myia-po-2024-fast-guards` | **actif** — tool-cache seedé (a2), ré-enregistrement sans UAC, jobs réels consommés |
| `myia-po-2025-fast-guards` | en préparation (pas de runner installé) |
| `myia-po-2026-fast-guards` | en préparation (pas de runner installé ; profil vérifié dans le registre) |

Le réglage GitHub « Require approval for all outside collaborators » complète la garde YAML ; il ne la remplace jamais. L'activation finale reste un geste explicite du user ou du coordinateur, après validation des tranches précédentes.
