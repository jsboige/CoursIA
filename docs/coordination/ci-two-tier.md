# CI à deux étages - inventaire mesuré des workflows (phase P0)

Plan : « CI à deux étages » (gardes et tests cibles à chaque push, suite lourde en lot quotidien sur l'arbre fusionné). Ce document est le livrable de la **phase P0** : quels workflows se déclenchent à chaque push de PR, combien ils coûtent, et lesquels sont lourds au sens du plan.

Mesure du **2026-11-09T19:06:30Z** (census et durées de run) et du **2026-11-10T02:18:27Z** (séparation **file / exécution**, mesurée par job — section 3.4). Tous les chiffres proviennent de `scripts/ci/measure_ci_two_tier.py` ; la commande de reproduction est en section 6.

Ce document **ne décide rien**. La bascule des gates (phase P4) appartient au coordinateur, avec sign-off du mainteneur ; ce document lui fournit l'inventaire sur lequel la décision s'appuie.

## 1. Ce que le PR gate exige aujourd'hui

Fait structurel, lu dans `scripts/pr_gate.py` :

- la protection de branche de `main` exige **un seul** nom de check : `PR gate` ;
- ce check est un **agrégateur** : il attend que tous les autres check-runs de la tête se concluent, et échoue si l'un d'eux échoue. Il ne porte aucune liste de workflows a maintenir à la main ;
- un check est **advisory** - donc hors du verdict du gate — quand le mot `advisory` figure dans le nom de son job ou dans le nom de son workflow (`pr_gate.is_advisory`).

Conséquence pour le plan : le gate n'exige pas « les workflows X, Y, Z » mais **tout job non-advisory déclenche sur `pull_request`**. L'inventaire de ces jobs vaut **77 jobs bloquants**, sur 94 jobs déclenchés sur `pull_request` (17 advisory). C'est cet ensemble-là qu'un deuxième étage devrait déplacer vers le lot quotidien.

Le point est structurant pour la suite : Déplacer un job de l'étage 1 vers l'étage 2 et le gate ne le voit plus — sauf si l'étage 2 émet, sur la tête de la PR, un check-run du meme nom. C'est la raison pour laquelle la phase P3 émet **à côté** des verdicts par push, et non à la place.

### 1.1 Ce qui existe déjà : la voie rapide

Le dépôt a déjà une première version de l'étage 1 : `scripts/ci/fast_lane.py` et son registre `scripts/ci/fast_lane_registry.py` mutualisent les gardes légères dans **un** checkout, puis émettent **un check-run nommé par garde** via l'API Checks. La granularité visible sur la PR est préservée, seule l'infrastructure est mutualisée ; c'est le modèle que l'étage 1 généralise aux tests cibles (phase P2).

Les registrations du registre sont des **tranches** : chacune porte un lot de gardes et leurs `paths`. La voie rapide est aujourd'hui dans un **mode mixte** : les gardes « absorbés » rendent leur verdict sous leur nom canonique, avec une conclusion réelle, et leur workflow dédié ne se déclenche plus sur `pull_request` ; les gardes du pilote restent en ombre préfixée et neutralisée, en attendant la comparaison. C'est exactement la forme que la phase P3 doit employer : un check-run du même nom,emplace du workflow d'origine.

**Ce que cela change pour l'inventaire.** Le déclencheur lu dans le YAML n'est plus synonyme de coût par push : un workflow dont la garde a été absorbée ne tourne plus sur `pull_request`. Le census de la section 2 est donc un **plafond** (déclencheurs déclarés), et non une mesure du coût effectif par push. Mesurer l'écart demanderait de recouper le registre d'absorption avec le plateau des checks d'une PR donnée - travail de la phase P3, quand le lot existe pour porter la comparaison.

## 2. Census des déclenchements

- **169** workflows dans `.github/workflows/` ;
- **71** se déclenchent sur `pull_request` ;
- **98** ne se déclenchent pas sur `pull_request` : ils ne sont pas dans le périmètre de la décroissance du coût par push, mais ils consomment le parc.

| Workflow | Déclencheurs |
|---|---|
| `adjacency-stale-sweep.yml` | schedule, workflow_dispatch |
| `ascii-flowchart-advisory.yml` | schedule, workflow_dispatch |
| `banner-guard.yml` | push, workflow_dispatch |
| `bare-cross-dir-load-gate.yml` | workflow_dispatch |
| `base-not-main-advisory.yml` | workflow_dispatch |
| `candidate-delivered-advisory.yml` | schedule, workflow_dispatch |
| `catalog-cron.yml` | schedule, workflow_dispatch |
| `cell-order-gate.yml` | workflow_dispatch |
| `check-resync-only.yml` | schedule, workflow_dispatch |
| `ci-overflow-controller.yml` | schedule, workflow_dispatch |
| `cjk-residue-advisory.yml` | schedule, workflow_dispatch |
| `closed-unmerged-pr-scan.yml` | schedule, workflow_dispatch |
| `concurrency-conj-guard.yml` | workflow_dispatch |
| `consecutive-code-cells-advisory.yml` | workflow_dispatch |
| `corroboration-python-nu.yml` | workflow_dispatch |
| `coursia-waiter-starvation-advisory.yml` | schedule, workflow_dispatch, workflow_run |
| `degenerate-figure-gate.yml` | workflow_dispatch |
| `degraded-mode-advisory.yml` | schedule, workflow_dispatch |
| `detect-dup-selftest.yml` | schedule, workflow_dispatch |
| `docs-link-check.yml` | workflow_dispatch |
| `dotnet-nuget-block-advisory.yml` | schedule, workflow_dispatch |
| `epic-charter-advisory.yml` | schedule, workflow_dispatch |
| `epic-neglect-sweep.yml` | schedule, workflow_dispatch |
| `evict-orphan-caches.yml` | push, workflow_run, schedule, workflow_dispatch |
| `exercise-leak-ci.yml` | workflow_dispatch |
| `exercises-advisory.yml` | schedule, workflow_dispatch |
| `fabricated-output-gate.yml` | workflow_dispatch |
| `fast-lane-shadow.yml` | workflow_dispatch |
| `grain-orphans-sweep.yml` | schedule, workflow_dispatch |
| `h1-hygiene-advisory.yml` | schedule, workflow_dispatch |
| `job-deaths-census-advisory.yml` | schedule, workflow_dispatch |
| `lane-claim-epic-wide-advisory.yml` | schedule, workflow_dispatch |
| `lane-claim-guard.yml` | workflow_dispatch |
| `leaky-fixture-sweep.yml` | schedule, workflow_dispatch |
| `lean-axiom.yml` | workflow_call |
| `lean-build.yml` | workflow_call |
| `linux-runner-starvation-advisory.yml` | schedule, workflow_dispatch, workflow_run |
| `linux-runner-version-pin-advisory.yml` | schedule, workflow_dispatch |
| `linux-self-hosted-tests.yml` | workflow_dispatch |
| `live-read-freshness.yml` | workflow_dispatch |
| `machine-dep-timing-advisory.yml` | schedule, workflow_dispatch |
| `machine-dep-timing-inventory.yml` | schedule, workflow_dispatch |
| `main-red-legibility.yml` | schedule, workflow_dispatch |
| `markdown-claims-output-advisory.yml` | workflow_dispatch |
| `markdown-deaccent-advisory.yml` | workflow_dispatch |
| `markdown-rendering-guard.yml` | push, workflow_dispatch |
| `markdown-table-guard.yml` | schedule, workflow_dispatch |
| `md-content-loss-gate.yml` | workflow_dispatch |
| `mermaid-fill-color-advisory.yml` | workflow_dispatch |
| `notebook-interp-positioning.yml` | workflow_dispatch |
| `notebook-nav-chain-guard.yml` | workflow_dispatch |
| `notebook-navlink-check.yml` | workflow_dispatch |
| `notebook-output-collapse-ratchet.yml` | workflow_dispatch |
| `notebook-output-failure-ratchet.yml` | workflow_dispatch |
| `notebook-output-flood-ratchet.yml` | workflow_dispatch |
| `organ-duplication-advisory.yml` | workflow_dispatch |
| `orphan-branch-scan.yml` | schedule, workflow_dispatch |
| `outputs-text-fragmentation-advisory.yml` | schedule, workflow_dispatch |
| `pip-leak-guard.yml` | workflow_dispatch |
| `pr-gate-rerun.yml` | workflow_dispatch |
| `pr-gate-stale-sweep.yml` | schedule, push, workflow_dispatch |
| `pr-gate-sweep-health-advisory.yml` | schedule, push, workflow_dispatch |
| `pr-path-collision-advisory.yml` | schedule, workflow_dispatch |
| `prose-counts-guard.yml` | workflow_dispatch |
| `qc-research-monitor.yml` | schedule, workflow_dispatch |
| `queue-ghost-watch.yml` | schedule, workflow_dispatch |
| `readme-ipynb-links-guard.yml` | push, workflow_dispatch |
| `regression-guard.yml` | workflow_dispatch |
| `render-volume-delta-advisory.yml` | schedule, workflow_dispatch |
| `repeated-prose-advisory.yml` | workflow_dispatch |
| `repo-size-advisory.yml` | schedule, workflow_dispatch |
| `review-coverage-advisory.yml` | schedule, workflow_dispatch |
| `runner-coresidence-advisory.yml` | schedule, workflow_dispatch |
| `runner-starvation-advisory.yml` | schedule, workflow_dispatch |
| `runner-variance-guard.yml` | schedule, workflow_dispatch |
| `scan-md-hierarchy-drift.yml` | workflow_dispatch |
| `series-naming-gate.yml` | push, workflow_dispatch |
| `site-links-post-deploy.yml` | workflow_run, workflow_dispatch |
| `slides-composition-advisory.yml` | schedule, workflow_dispatch |
| `slow-lane.yml` | schedule, workflow_dispatch |
| `split-reading-advisory.yml` | workflow_dispatch |
| `stale-base-warning.yml` | workflow_dispatch |
| `stale-guard-red-sweep.yml` | schedule, workflow_dispatch |
| `stale-pr-branches-sweep.yml` | schedule, workflow_dispatch |
| `svg-broken-geometry-gate.yml` | workflow_dispatch |
| `svg-decimal-comma-gate.yml` | workflow_dispatch |
| `svg-empty-display-gate.yml` | workflow_dispatch |
| `svg-offscreen-flat-gate.yml` | workflow_dispatch |
| `testpaths-coverage-guard.yml` | workflow_dispatch |
| `translation-hot-drift-advisory.yml` | workflow_dispatch |
| `translation-parity.yml` | schedule, workflow_dispatch |
| `translation-sync.yml` | workflow_dispatch |
| `twin-parity-cron.yml` | schedule, workflow_dispatch |
| `twin-parity-drift-audit.yml` | schedule, workflow_dispatch |
| `variation-light-genre.yml` | workflow_dispatch |
| `variation-tag-guard.yml` | issue_comment, workflow_dispatch |
| `windows-self-hosted-tests.yml` | workflow_dispatch |
| `workflow-path-filter-audit.yml` | schedule, workflow_dispatch |

Les déclencheurs sont lus dans le bloc `on:` de chaque YAML, pas par une recherche de texte : plusieurs workflows mentionnent `pull_request` dans un commentaire (pour dire qu'ils en sont **sortis**) et un grep les compterait à tort. La lecture du bloc `on:` est ce qui fait la différence entre les deux colonnes.

## 3. Le classement

Critère du plan : **lourd** = médiane > 5 min, ou p90 > 15 min, ou besoin de Lean, de papermill ou du réseau. La mesure porte sur les runs `pull_request` **terminés** ; la durée est `updated_at - run_started_at`. Les runs annulés et les runs `skipped` (durée nulle) sont comptés dans les conclusions mais exclus des percentiles : un run annulé dit que la file sature, pas que le code est cassé.

Fenêtre mesurée : **2026-11-09T15:31:14Z -> 2026-11-09T19:02:13Z** (1000 runs `pull_request` relevés).

Sur les 71 workflows déclenchés sur `pull_request`, **51** ont au moins un run `pull_request` terminé et donc une durée mesurable ; **20** n'en ont aucun sur la fenêtre interrogée (workflow récemment ajouté, ou déclenche par autre chose que `pull_request` sur la fenêtre). Ceux-là sont classés par leurs signaux déclarés, pas par leur durée : la mesure reste à faire.

### 3.1 Les workflows lourds

| Workflow | Jobs | Runs PR | Médiane run (min) | p90 run (min) | Max run (min) | Signaux |
|---|---:|---:|---:|---:|---:|---|
| `notebook-outputs-required.yml` | 2 | 26 | 1.9 | 112.2 | 145.2 | durée mesurée, papermill |
| `validation-matrix.yml` | 1 | 26 | 1.9 | 105.3 | 131.4 | durée mesurée, papermill, réseau |
| `source-output-ratchet.yml` | 1 | 21 | 5.4 | 102.4 | 110.9 | durée mesurée, papermill |
| `translation-guard.yml` | 1 | 8 | 0.2 | 87.5 | 98.6 | durée mesurée |
| `scripts-tests.yml` | 3 | 28 | 11.7 | 84.6 | 100 | durée mesurée, papermill, réseau |
| `bash-syntax-advisory.yml` | 3 | 2 | 40 | 69.6 | 77 | durée mesurée |
| `lean-visibility-advisory.yml` | 1 | 3 | 2.9 | 52.1 | 64.3 | durée mesurée |
| `pr-gate.yml` | 1 | 30 | 3 | 17.6 | 44.4 | durée mesurée, réseau |
| `codeql.yml` | 2 | 14 | 8.2 | 13.5 | 17.8 | durée mesurée |
| `ict-tests.yml` | 1 | 3 | 10.5 | 10.7 | 10.7 | durée mesurée, réseau |
| `secret-scan.yml` | 4 | 29 | 3.4 | 9.2 | 10.5 | réseau |
| `always-on-guards.yml` | 1 | 29 | 5.8 | 8.9 | 15.2 | durée mesurée, réseau |
| `slides-build-advisory.yml` | 1 | 2 | 6.2 | 8.6 | 9.2 | durée mesurée, réseau |
| `notebook-execution-required.yml` | 3 | 26 | 3.1 | 7.7 | 11.8 | papermill, réseau |
| `quarto-pages-deploy.yml` | 5 | 26 | 3.4 | 5.6 | 9.1 | réseau |
| `catalog-drift.yml` | 1 | 26 | 2.2 | 5 | 8.7 | réseau |
| `twin-parity.yml` | 2 | 20 | 2.2 | 4.9 | 10.1 | papermill, réseau |
| `notebook-validation.yml` | 1 | 20 | 1.6 | 4.7 | 10.7 | réseau |
| `notebook-math-render.yml` | 1 | 25 | 1.3 | 4.5 | 5.8 | réseau |
| `notebook-kernel-drift-guard.yml` | 1 | 25 | 1.4 | 4.2 | 6.4 | réseau |
| `notebook-papermill-ratchet.yml` | 1 | 26 | 1.5 | 4 | 7.8 | papermill, réseau |
| `notebook-exec-sequence-ratchet.yml` | 1 | 28 | 1.4 | 3.9 | 5.3 | réseau |
| `always-on-commenters.yml` | 1 | 29 | 1.7 | 3.5 | 8 | réseau |
| `gametheory-tests.yml` | 1 | 5 | 2.3 | 3.1 | 3.3 | réseau |
| `creation-provenance-advisory.yml` | 1 | 20 | 0.9 | 2.5 | 7.9 | réseau |
| `always-on-metadata-guards.yml` | 1 | 43 | 0.8 | 2.1 | 9.8 | réseau |
| `slides-composition-pr-relay.yml` | 1 | 2 | 1.3 | 1.8 | 1.9 | réseau |
| `lean-ci-matrix.yml` | 2 | 3 | 0.9 | 1.2 | 1.2 | Lean |

Workflows à signaux déclarés, sans run `pull_request` terminés sur la fenêtre :

| Workflow | Jobs | Signaux |
|---|---:|---|
| `arxiv-attributions-guard.yml` | 1 | réseau |
| `assert-memory-budget.yml` | 1 | réseau |
| `dotnet-Shared.Tests.yml` | 2 | réseau |
| `genai-helpers-tests.yml` | 1 | réseau |
| `geometry-tests.yml` | 1 | réseau |
| `hooks-parity.yml` | 1 | réseau |
| `ict-tests-profile.yml` | 1 | réseau |
| `label-paths-guard.yml` | 1 | réseau |
| `ml-tests.yml` | 2 | réseau |
| `owui-playwright-check.yml` | 1 | réseau |
| `quantconnect-notebook-freshness.yml` | 1 | réseau |
| `sudoku-tests.yml` | 1 | réseau |
| `unique-check-run-names-guard.yml` | 1 | réseau |

### 3.2 Les workflows légers

| Workflow | Jobs | Runs PR | Médiane run (min) | p90 run (min) |
|---|---:|---:|---:|---:|
| `local-path-waiver-guard.yml` | 1 | 29 | 0.4 | 3.5 |
| `twin-attestation-name-guard.yml` | 1 | 16 | 0.6 | 3.7 |
| `perimeter-review-guard.yml` | 1 | 43 | 0.8 | 3.4 |
| `harness-coauthor-guard.yml` | 1 | 2 | 0.9 | 1.5 |
| `notebook-latex-control-chars.yml` | 1 | 26 | 1.3 | 4.7 |
| `submodule-drift.yml` | 1 | 1 | 1.3 | 1.3 |
| `notebook-cell-source-parses.yml` | 1 | 26 | 1.5 | 5.4 |
| `notebook-plan-loss-gate.yml` | 1 | 43 | 1.5 | 4.1 |
| `solution-leak-guard.yml` | 1 | 20 | 1.5 | 4 |
| `translation-drift.yml` | 1 | 21 | 1.6 | 5.4 |
| `twin-index-collision-gate.yml` | 1 | 16 | 1.6 | 7.7 |
| `bios-companion-coverage.yml` | 1 | 16 | 1.7 | 4 |
| `lean-i18n-drift.yml` | 1 | 2 | 1.7 | 2 |
| `pedagogy-density-advisory.yml` | 2 | 27 | 1.7 | 4.5 |
| `always-on-guards-body.yml` | 1 | 42 | 1.9 | 3.5 |
| `enrich-quality-gate.yml` | 1 | 20 | 1.9 | 4.8 |
| `quarto-render-list-freshness.yml` | 1 | 26 | 1.9 | 3.8 |
| `lean-derived-pages-gate.yml` | 1 | 2 | 2 | 2.3 |
| `cycle-time-guard.yml` | 1 | 14 | 2.2 | 7.1 |
| `paragraph-length-advisory.yml` | 1 | 21 | 2.2 | 4.1 |
| `docs-transients-guard.yml` | 1 | 14 | 2.3 | 6.9 |
| `notebook-link-render-check.yml` | 1 | 14 | 2.3 | 4.3 |
| `docs-reference-guard.yml` | 1 | 14 | 2.8 | 4.7 |

### 3.3 Ce que la mesure ne dit pas

- **La fenetre est courte et elle est annoncée.** L'API Actions plafonne la pagination a 1000 résultats filtrés (au-dela, la page revient vide) : la fenetre réellement couverte est donc la plus récente, **2026-11-09T15:31:14Z -> 2026-11-09T19:02:13Z** (1000 runs `pull_request`). Les effectifs sont des effectifs de cette fenetre, pas des effectifs de la semaine ; l'intervalle est écrit dans le JSON (`window_covered`), il n'est jamais supposé.
- **Le balayage est global, pas par workflow.** Les runs sont lus une fois pour tout le dépôt, puis regroupés par workflow : un workflow peu sollicite n'a que quelques runs dans la fenetre, et sa médiane porte sur ces quelques runs.
- **La durée d'un workflow est celle de son job le plus lent**, pas la somme des jobs. Un workflow a cinq jobs parallèles ne coûte pas cinq fois plus.
- **La durée d'un run est la somme de deux choses distinctes.** `updated_at - run_started_at` mesure le temps écoulé entre le démarrage du run et sa fin : cela inclut l'**attente dans la file des runners** autant que l'exécution. Une durée de run n'est donc pas une mesure de coût de garde, et elle ne dit rien du checkout. C'est pourquoi les tableaux 3.1 et 3.2 nomment leurs colonnes « run », et pourquoi la section 3.4 sépare les deux postes.

### 3.4 La file et l'exécution, mesurées par job

La durée d'un run confond deux postes qu'il faut distinguer : le temps **passé en file** avant que le runner ne prenne le job, et le temps **d'exécution** du job lui-même.

- attente = `started_at - created_at` (le job attend un runner) ;
- exécution = `completed_at - started_at` (le job tourne) ;
- la part du **checkout** dans l'exécution est celle de l'organe natif `scripts/ci/measure_checkout_p90.py` (#25519), réutilisé tel quel : la définition de « durée de checkout » reste la sienne.

**Échantillonnage** (écrit dans le JSON, `jobs_measure.sampling`) : **60 runs terminés** de la fenêtre **2026-11-09T23:55:29Z -> 2026-11-10T02:15:20Z**, au plus **3 runs par workflow** (les plus récents terminés), plafond global 60 — **30 workflows**, **79 jobs**, aucun job sans fin. Seuls des runs `completed` sont retenus : un run en cours n'a pas de `completed_at` et biaiserait la mesure.

| Workflow | Jobs | Attente méd. | Attente p90 | Exécution méd. | Exécution p90 | Checkout p90 | part checkout / exécution | part attente / total |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `local-path-waiver-guard.yml` | 3 | 2.73 | 3.39 | 0.12 | 0.13 | 0.03 | 0.23 | 0.96 |
| `always-on-metadata-guards.yml` | 3 | 2.43 | 3.85 | 0.23 | 0.47 | 0.1 | 0.21 | 0.89 |
| `notebook-plan-loss-gate.yml` | 3 | 3.3 | 3.47 | 0.97 | 1.13 | - | - | 0.75 |
| `notebook-link-render-check.yml` | 2 | 1.88 | 3.2 | 1.03 | 1.05 | 0.95 | 0.91 | 0.75 |
| `perimeter-review-guard.yml` | 12 | 0 | 1.25 | 0 | 0.45 | 0.08 | 0.18 | 0.73 |
| `secret-scan.yml` | 4 | 1.23 | 3.74 | 1.12 | 1.36 | 0.9 | 0.66 | 0.73 |
| `paragraph-length-advisory.yml` | 3 | 2.05 | 2.97 | 1.18 | 1.18 | - | - | 0.72 |
| `notebook-papermill-ratchet.yml` | 2 | 2.52 | 2.8 | 1.12 | 1.16 | 0.95 | 0.82 | 0.71 |
| `translation-drift.yml` | 2 | 1.66 | 2.93 | 1.26 | 1.28 | - | - | 0.7 |
| `quarto-render-list-freshness.yml` | 2 | 1.53 | 2.71 | 1.17 | 1.21 | - | - | 0.69 |
| `notebook-exec-sequence-ratchet.yml` | 3 | 0.33 | 2.6 | 1.08 | 1.19 | 1.02 | 0.86 | 0.69 |
| `notebook-validation.yml` | 2 | 1.46 | 2.24 | 1.4 | 1.47 | 1.06 | 0.72 | 0.6 |
| `pedagogy-density-advisory.yml` | 2 | 0.9 | 1.62 | 1.07 | 1.07 | - | - | 0.6 |
| `notebook-cell-source-parses.yml` | 2 | 1.48 | 2.07 | 1.27 | 1.44 | 1.32 | 0.92 | 0.59 |
| `always-on-commenters.yml` | 3 | 1.17 | 1.73 | 1.33 | 1.39 | 1.1 | 0.79 | 0.55 |
| `always-on-guards-body.yml` | 3 | 0.42 | 1.78 | 1.58 | 1.7 | 1.06 | 0.62 | 0.51 |
| `always-on-guards.yml` | 2 | 2.07 | 2.48 | 2.39 | 2.48 | 0.92 | 0.37 | 0.5 |
| `solution-leak-guard.yml` | 1 | 1.07 | 1.07 | 1.08 | 1.08 | 0.9 | 0.83 | 0.5 |
| `notebook-math-render.yml` | 2 | 0.99 | 1.19 | 1.26 | 1.37 | 1.11 | 0.81 | 0.47 |
| `cycle-time-guard.yml` | 2 | 0.48 | 0.82 | 1.02 | 1.07 | 0.99 | 0.93 | 0.43 |
| `quarto-pages-deploy.yml` | 5 | 0 | 1.46 | 0 | 2.09 | - | - | 0.41 |
| `lean-i18n-drift.yml` | 1 | 0.48 | 0.48 | 0.98 | 0.98 | 0.88 | 0.9 | 0.33 |
| `docs-reference-guard.yml` | 2 | 0.32 | 0.53 | 1.08 | 1.15 | 1.08 | 0.94 | 0.32 |
| `lean-derived-pages-gate.yml` | 1 | 0.5 | 0.5 | 1.53 | 1.53 | - | - | 0.25 |
| `catalog-drift.yml` | 2 | 0.73 | 1.19 | 2.77 | 3.73 | - | - | 0.24 |
| `arxiv-attributions-guard.yml` | 1 | 0.22 | 0.22 | 1.02 | 1.02 | - | - | 0.18 |
| `lean-visibility-advisory.yml` | 1 | 0.05 | 0.05 | 0.65 | 0.65 | - | - | 0.07 |
| `validation-matrix.yml` | 2 | 0.06 | 0.07 | 1.5 | 2.38 | 2.09 | 0.88 | 0.03 |
| `notebook-outputs-required.yml` | 4 | 0.05 | 0.06 | 0.35 | 2.74 | 2.56 | 0.93 | 0.02 |
| `source-output-ratchet.yml` | 2 | 0.05 | 0.06 | 2.02 | 3.4 | - | - | 0.02 |

**Ce que dit cette mesure** (médiane sur les 30 workflows) :

| Poste | p90 médian | part médiane |
|---|---:|---:|
| Attente (file) | **1.68 min** (max 3.85) | **0.53** du total du job |
| Exécution | **1.20 min** (max 3.73) | 0.47 du total du job |
| Checkout, **à l'intérieur** de l'exécution | - | **0.82** de l'exécution p90 |

Deux lectures, et elles ne disent pas la même chose :

- **Le checkout domine l'exécution** : à l'intérieur du temps où le job tourne, le checkout est **82 %** du p90 (médiane sur les workflows où l'étape est reconnue). La phase P1 attaque donc un poste **réel**.
- **Mais la file domine le total** : le temps passé en attente d'un runner représente **53 %** du p90 total du job (médiane), contre 47 % pour l'exécution. Ramener le checkout à zéro ne ferait tomber que la moitié de l'étage 1 — **l'autre moitié est de la contention de runners**.

C'est le renversement que la mesure impose : le p90 « lourd » d'un garde n'est pas un garde lent, c'est un job qui a attendu. L'attente n'est d'ailleurs pas proportionnelle au nombre de jobs du workflow : `perimeter-review-guard.yml` déclenche **12** jobs pour un p90 d'attente de 1,25 min, tandis que `local-path-waiver-guard.yml` déclenche **1** job et attend **3,39 min**. Ce que la mesure établit, c'est que l'attente existe, qu'elle n'est pas imputable au travail du garde, et qu'elle est du même ordre de grandeur que l'exécution.

**Ce que cette mesure ne voit pas.** L'attente du **run** lui-même — le temps entre la création du run et le démarrage de ses jobs — n'est pas dans la file du job : elle précède la création des jobs. Elle reste lisible dans la durée de run des tableaux 3.1 et 3.2, qui est donc conservée telle quelle, mais elle n'est pas décomposée ici. La file et l'exécution mesurées ici sont les deux postes **intra-job**.

## 4. Lecture pour les phases suivantes

Ce que l'inventaire établit, et ce qu'il n'établit pas. **L'ordre des phases se déduit de la mesure 3.4, il n'est plus supposé** :

- **Le premier levier est le nombre de jobs déclenchés par push** (P2 et P3), pas le checkout. La file d'attente des runners représente **53 %** du p90 total d'un job (médiane sur 30 workflows), contre 47 % pour l'exécution : réduire le nombre de jobs déclenchés attaque le poste dominant. C'est ce que P2 (déclasser la suite de scripts en étage 2) et P3 (mutualiser les gardes dans le lot quotidien) font.
- **P1 (checkout) reste un levier réel, mais de second rang.** À l'intérieur de l'exécution, le checkout en est **82 %** du p90 : l'escamoter ne fait tomber que la moitié de l'étage 1. La mesure « avant / après » du p90 de checkout se fait sur les workflows du tableau du plan, **en regard de la part d'attente** — sans quoi une baisse du checkout se lit à tort comme une baisse du coût total.
- **P2 (tests cibles)** porte sur la suite de scripts : c'est un workflow unique et lourd ; le déclasser en étage 2 est le gain le plus direct du plan.
- **P3 (lot quotidien)** doit émettre, sur chaque tête du lot, un check-run **du même nom** que celui du push, sinon le gate ne voit rien. Le point est pose en section 1.
- **P4 (bascule)** n'est pas décidee par ce document.

## 5. Vérifications

- le script se lance depuis la racine du dépôt, sans dépendance tierce hors `gh` ;
- il ne modifie rien dans le dépôt et n'écrit aucun secret ;
- la liste des jobs bloquants est produite par `pr_gate.is_advisory`, la fonction du gate lui-meme : si le gate change de règle, l'inventaire suit.

## 6. Reproduction

```bash
python scripts/ci/measure_ci_two_tier.py --hours 24 \
    --jobs-par-workflow 3 --jobs-plafond 60 \
    --out .tmp/ci_two_tier_inventory.json
```

Le script balaye les runs `pull_request` du dépôt par pages de 100 (balayage global : les runs sont lus une fois, puis regroupés par workflow), lit le census des workflows dans les fichiers locaux, et écrit les durées **et** la liste des jobs déclenchés sur `pull_request`. Il ne modifie rien dans le dépôt et n'écrit aucun secret.

La phase `jobs_measure` descend ensuite au niveau du job (`/actions/runs/{id}/jobs`) sur un échantillon **borné et écrit** : au plus `--jobs-par-workflow` runs **terminés** par workflow (les plus récents de la fenêtre), plafond global `--jobs-plafond`. Elle sépare l'**attente** (`started_at - created_at`) de l'**exécution** (`completed_at - started_at`) et reprend la part du checkout de l'organe natif `scripts/ci/measure_checkout_p90.py`. `--sans-jobs` se limite au census.

