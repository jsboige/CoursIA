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

## Tranches suivantes, non activées

La préparation complète reste découpée :

1. **Mesure** — instrument de cette page.
2. **Isolation** — compte OS dédié sans accès à `.secrets/`, SSH ou keyring `gh`; runner éphémère et runner group restreint; scripts d'enrôlement et de teardown idempotents avec `--dry-run`.
3. **Commutation** — un seul point de bascule et garde `github.event.pull_request.head.repo.full_name == github.repository`; aucun `pull_request_target` auto-hébergé.
4. **Preuve contrôlée** — une exécution légère réussie, un contrôle négatif fork/payload, puis teardown et preuve que l'état initial est restauré.

Le token d'enregistrement ne doit jamais apparaître dans un commit, une PR, un commentaire GitHub ou un dashboard. L'activation finale reste un geste explicite du user ou du coordinateur, après validation des tranches précédentes.
