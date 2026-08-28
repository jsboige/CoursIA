# Préparation des runners GitHub Actions auto-hébergés

Cette page décrit les mesures et les garde-fous du chantier #12704. **Aucun runner n'est enregistré ni activé par cette première tranche.** Le dépôt `jsboige/CoursIA` est public : une PR de fork peut contenir du code non fiable. Toute future exécution auto-hébergée devra donc être réservée aux branches du dépôt lui-même, avec une garde YAML explicite en plus des réglages GitHub.

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

## Amorcer le cache d'outils, et pourquoi le fichier témoin porte tout

Le compte de service dédié n'a **aucun Python accessible**. Ce n'est pas une supposition :
le run `33087876304` (branche `fix/13217`, 2026-08-27T16:00Z) échoue en deux secondes sur
`The term 'python' is not recognized`. Les interpréteurs de la flotte sont des installations
*per-user* sous `AppData/Local/Programs/Python`, donc hors du `PATH` système **et** hors des
ACL du compte de service, que l'installation retire de l'héritage.

C'est la raison pour laquelle `actions/setup-python` est **conservé** dans
`windows-self-hosted-tests.yml`, et pour laquelle la PR qui le retirait au profit du Python
machine (#13233) est fermée : elle suppose un `PATH` que le compte de service n'a pas.

L'amorçage se fait donc côté machine, en peuplant le cache d'outils du runner :

```
<workdir>/_work/_tool/Python/3.11.9/x64/        arbre Python complet
<workdir>/_work/_tool/Python/3.11.9/x64.complete   fichier témoin
```

**Le fichier témoin n'est pas une formalité : sans lui, l'amorçage est détruit par le premier
job.** `tc.find()` ne consulte que le témoin. S'il manque, l'arbre peuplé juste à côté est
invisible : `setup-python` annonce `Version 3.11 was not found in the local cache`, télécharge
l'archive, et son `install.ps1` trouve alors le répertoire existant, **le supprime**, puis y
copie ce que l'archive contient réellement — l'installeur, pas un arbre, car les paquets
`actions/python-versions` embarquent un exécutable. Il tente enfin de le jouer sous le compte
de service et échoue en `0x80070005`. Un cache amorcé sans témoin est donc *pire* qu'un cache
absent : il est effacé, et l'erreur qui en résulte ne nomme jamais la cause.

Avec le témoin, le job touche le cache immédiatement : aucun `setup.ps1` exécuté, aucun
téléchargement, et la dépendance à l'`ExecutionPolicy` du compte de service disparaît — c'est
elle qui bloquait la lane (`UnauthorizedAccess` sur `setup.ps1`, #13217).

Mesures d'acceptation sur po-2024, variante déployée :

| Run | Branche | Résultat |
|---|---|---|
| `33092567324` | `main` | `setup-python` succès, 39 passés / 1 échec — l'échec est l'invariant #13238, côté dépôt |
| `33093119578` | branche de correction | **42 passés**, conclusion `success` |

L'amorçage est à refaire sur **chaque** machine qui porte un runner : il vit dans le workdir,
que le teardown retire. Un runner ré-enregistré sur une machine non amorcée retombe dans la
séquence destructrice ci-dessus.

## Tranches suivantes, non activées

La préparation complète reste découpée :

1. **Mesure** — instrument de cette page.
2. **Isolation statique** — scanner fail-closed, allowlist et labels dépôt.
3. **Cycle de vie local** — gestionnaire, profils, probes et teardown décrits ci-dessus.
4. **Commutation** — un seul point de bascule et garde `github.event.pull_request.head.repo.full_name == github.repository`; aucun `pull_request_target` auto-hébergé.
5. **Preuve contrôlée** — autorisation explicite, une exécution légère réussie, contrôle négatif fork/payload, puis teardown et preuve que l'état initial est restauré.

Le réglage GitHub « Require approval for all outside collaborators » complète la garde YAML ; il ne la remplace jamais. L'activation finale reste un geste explicite du user ou du coordinateur, après validation des tranches précédentes.
