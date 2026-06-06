# Index de la documentation

Ce repertoire centralise la documentation projet deportee du CLAUDE.md. Chaque fichier documente un aspect precis du projet CoursIA (infrastructure, procedures, regles, etat des series).

## Documentation generale

Ces fichiers decrivent l'architecture et le fonctionnement general du projet.

| Fichier | Description |
|---------|-------------|
| [common-commands.md](common-commands.md) | Environnement, validation notebooks, scripts CLI |
| [procedures-recurrentes.md](procedures-recurrentes.md) | Workflow PR, dispatch, validation, pre-commit |
| [architecture_mcp_roo.md](architecture_mcp_roo.md) | Architecture des 34 outils MCP roo-state-manager |
| [kernels-runtime.md](kernels-runtime.md) | .NET, Python, WSL, conda envs |
| [env-python-reparation.md](env-python-reparation.md) | RepARATION environnements Python |
| [handson-book-mapping.md](_archives/handson-book-mapping.md) | Cartographie du livre Hands-On AI Trading (Jared Broad) |
| [qc-broken-strategies-audit.md](_archives/qc-broken-strategies-audit.md) | Audit strategies QuantConnect broken |
| [visitor-navigation-guide.md](visitor-navigation-guide.md) | Carte du visiteur : 4 parcours thematiques a travers 511 notebooks |
| [grothendieckian-lens.md](grothendieckian-lens.md) | Cle de lecture grothendieckienne : mer qui monte, grades A/B/C, table grounded |

## Regles et conventions

Regles de travail du cluster, autochargees via `.claude/rules/` ou documentees ici.

| Fichier | Emplacement | Description |
|---------|-------------|-------------|
| pr-review-discipline.md | `.claude/rules/` | Criteres CHANGES_REQUESTED pour reviews |
| git-workflow.md | `.claude/rules/` | Branches, commits, force push interdite |
| anti-regression.md | `.claude/rules/` | Preserver preuves et code existant |
| audit-reassessment.md | `.claude/rules/` | Protocole verification avant fix |
| verify-before-claiming.md | `.claude/rules/` | Verification AVANT diagnostic |
| code-style.md | `.claude/rules/` | PEP8, C#, conventions |
| notebook-conventions.md | `.claude/rules/` | C.1-C.3 : pas d'erreur, outputs, Papermill |
| exercise-example-labeling.md | `.claude/rules/` | Labeling Exemple/Exercice content-based |
| secrets-hygiene.md | `.claude/rules/` | Gestion des secrets |
| lean-merge-discipline.md | `.claude/rules/` | Lake build avant merge |
| student-pr-reviews.md | `.claude/rules/` | Reviews PR etudiantes |
| coordinator-discipline.md | `.claude/rules/` | Merge actif coordinateur |
| proactive-coordination.md | `.claude/rules/` | 1 PR/wakeup + side-track async |
| user-blocker-signaling.md | `.claude/rules/` | Signaler bloqueurs user |
| harness-hygiene.md | `.claude/rules/` | Hygiene harness |
| wsl-kernels.md | `.claude/rules/` | WSL pour kernels notebook |
| genai-config.md | `.claude/rules/` | Docker GPU config |

## Documentation projet (detaillee)

Ces fichiers fournissent des details complementaires au CLAUDE.md principal.

| Fichier | Description |
|---------|-------------|
| [pr-review-context.md](pr-review-context.md) | Contexte incidents + anti-patterns reviews |
| [proactive-coordination-detail.md](proactive-coordination-detail.md) | Backlog 8 sources, mapping machines, cadence |
| [regles-vigilance-detail.md](regles-vigilance-detail.md) | Details G.1-G.9 + incidents |
| [regles-validation-detail.md](regles-validation-detail.md) | Details H.1-H.7 + incident Sudoku-13 |
| [scripts-reference.md](scripts-reference.md) | Catalogue scripts depot |
| [subagents-reference.md](subagents-reference.md) | Roster 21 agents + 15 skills |
| [student-pr-reviews-detail.md](student-pr-reviews-detail.md) | Incident, format public, workflow |
| [secrets-and-coord-detail.md](secrets-and-coord-detail.md) | Secrets + coordination cross-machine |
| [user-blocker-signaling-detail.md](user-blocker-signaling-detail.md) | Categories + anti-patterns signaler |
| [wsl-kernels-detail.md](wsl-kernels-detail.md) | Details WSL kernels |
| [integration-roadmap.md](_archives/integration-roadmap.md) | Roadmap integration |
| [claude-code-config.md](claude-code-config.md) | Agents, skills, rules, model selection |

## Infrastructure et agents

| Fichier | Description |
|---------|-------------|
| [cluster-agents.md](cluster-agents.md) | Machines cluster, GPU topology |
| [teaching-context.md](teaching-context.md) | Calendrier, scope EPITA-IS, agents par ecole |
| [env-audit-cluster-2026-05-10.md](_archives/env-audit-cluster-2026-05-10.md) | Audit environnements cluster |

## Grading / Notation

| Fichier | Description |
|---------|-------------|
| [ece-grading.md](ece-grading.md) | Pipeline GradeBookApp (EPITA-ECE) |
| [esgf-grading.md](esgf-grading.md) | Pipeline ESGF (cohorte ESGF, calibration) |

## QuantConnect

| Fichier | Description |
|---------|-------------|
| [quantconnect.md](quantconnect.md) | Backtests, structure, livre reference |
| [qc-comparative-backtests.md](qc-comparative-backtests.md) | Analyse comparative backtests multi-strategies |

## GenAI (docs/genai/)

Documentation detailee de l'infrastructure GenAI (ComfyUI, Docker, modeles locaux).

| Fichier | Description |
|---------|-------------|
| [genai-services.md](genai-services.md) | Architectures Qwen/Lumina, mapping notebooks |
| [genai/README.md](_archives/genai/README.md) | Index services GenAI |
| [genai/user-guide.md](_archives/genai/user-guide.md) | Guide utilisateur |
| [genai/architecture.md](_archives/genai/architecture.md) | Architecture GenAI |
| [genai/deployment-guide.md](_archives/genai/deployment-guide.md) | Guide deploiement |
| [genai/docker-orchestration.md](_archives/genai/docker-orchestration.md) | Orchestration Docker |
| [genai/docker-specs.md](_archives/genai/docker-specs.md) | Specs Docker |
| [genai/environment-configurations.md](_archives/genai/environment-configurations.md) | Configs environnement |
| [genai/troubleshooting.md](_archives/genai/troubleshooting.md) | Resolution problems |
| [genai/infrastructure-tests.md](_archives/genai/infrastructure-tests.md) | Tests infrastructure |
| [genai/development-standards.md](_archives/genai/development-standards.md) | Standards developpement |
| [genai/docker-lifecycle-management.md](_archives/genai/docker-lifecycle-management.md) | Gestion cycle de vie Docker |
| [genai/ecosystem-readme.md](_archives/genai/ecosystem-readme.md) | Ecosystem GenAI |
| [genai/integration-procedures.md](_archives/genai/integration-procedures.md) | Procedures integration |
| [genai/phase2-templates.md](_archives/genai/phase2-templates.md) | Templates phase 2 |
| [genai/powershell-scripts.md](_archives/genai/powershell-scripts.md) | Scripts PowerShell |

## Lean (docs/lean/)

Iteration history prover, intractable diagnosis, LLM endpoints.

| Fichier | Description |
|---------|-------------|
| [lean/coordinator-workflow.md](lean/coordinator-workflow.md) | Workflow coordinateur |
| [lean/llm-endpoints.md](lean/llm-endpoints.md) | Endpoints LLM |
| [lean/prover_iteration_history.md](lean/prover_iteration_history.md) | Historique iteration prover |
| [lean/sota-2026-analysis.md](lean/sota-2026-analysis.md) | Analyse SOTA 2026 |
| [lean/stable_marriage_intractable_diagnosis.md](lean/stable_marriage_intractable_diagnosis.md) | Diagnosis intractable stable marriage |

## Parcours d'apprentissage (docs/parcours/)

Guides pedagogiques pour les parcours d'apprentissage.

| Fichier | Description |
|---------|-------------|
| [parcours/ia-classique.md](parcours/ia-classique.md) | IA classique |
| [parcours/ia-symbolique.md](parcours/ia-symbolique.md) | IA symbolique |
| [parcours/recherche.md](parcours/recherche.md) | Recherche |
| [parcours/trading.md](parcours/trading.md) | Trading |
| [parcours/genai.md](parcours/genai.md) | GenAI |

## Curriculum (docs/curriculum/)

| Fichier | Description |
|---------|-------------|
| [curriculum/stage5_mamba_ssm.md](curriculum/stage5_mamba_ssm.md) | Stage 5 Mamba/SSM |

## Analyse et tracking

| Fichier | Description |
|---------|-------------|
| [ml-trading-state.md](ml-trading-state.md) | Etat actif ML trading |
| [audit-reassessment-findings.md](audit-reassessment-findings.md) | Findings reassessment |
| [catalog_markers.md](catalog_markers.md) | Catalog markers |
| [analysis/qc-notebooks-exec-classification.md](analysis/qc-notebooks-exec-classification.md) | Classification execution notebooks QC |
| [research/dl_predictability_finance_2026.md](research/dl_predictability_finance_2026.md) | Predictibilite DL finance 2026 |
| [templates/student-pr-template.md](templates/student-pr-template.md) | Template PR etudiante |

## Historique et archives

Ces documents sont conserves pour reference mais ne sont plus actifs.

| Fichier | Description |
|---------|-------------|
| [01-cartographie-initiale.md](_archives/01-cartographie-initiale.md) | Cartographie initiale projet |
| [02-etude-adk-deepmind.md](_archives/02-etude-adk-deepmind.md) | Etude DeepMind ADK |
| [03-plan-formation-datascience-agentique.md](_archives/03-plan-formation-datascience-agentique.md) | Plan formation data science agentique |
| [GROTHENDIECK_MATHLIB_MAP.md](_archives/GROTHENDIECK_MATHLIB_MAP.md) | Map Mathlib Grothendieck |
| [H7_P2_DOCKER_ERROR_CATALOG.md](_archives/H7_P2_DOCKER_ERROR_CATALOG.md) | Catalog erreurs Docker H7/P2 |
| [NOTEBOOK_ENV_COVERAGE.md](_archives/NOTEBOOK_ENV_COVERAGE.md) | Couverture environnements notebooks |
| [REVERSE_PROXY_CIRCUIT.md](_archives/REVERSE_PROXY_CIRCUIT.md) | Reverse proxy circuit |
| [STABLE_SNAPSHOT.md](STABLE_SNAPSHOT.md) | Stable snapshot |
| [epf-universalisation-design.md](_archives/epf-universalisation-design.md) | Design universalisation EPF |
| [epic-1028-audiobook-postmortem.md](_archives/epic-1028-audiobook-postmortem.md) | Postmortem audiobook |
| [dette-branches-audit-2026-05-27.md](_archives/dette-branches-audit-2026-05-27.md) | Dette branches audit |
| [genai-images-mission-complete.md](_archives/genai-images-mission-complete.md) | Mission complete images GenAI |
| [genai-services-inventory-2026-05.md](_archives/genai-services-inventory-2026-05.md) | Inventory services GenAI mai 2026 |
| [genai-stack-audit-2026-05-10.md](_archives/genai-stack-audit-2026-05-10.md) | Audit stack GenAI |
| [qc-league-ece.md](_archives/qc-league-ece.md) | League ECE QuantConnect |
| [qc-stabilization-phase2.md](_archives/qc-stabilization-phase2.md) | Stabilisation QC phase 2 |
| [qc-strategies-status.md](qc-strategies-status.md) | Status strategies QuantConnect |
| [slides-refonte-procedure.md](_archives/slides-refonte-procedure.md) | Procedure refonte slides |
| [stabilization-phase1-matrix.md](_archives/stabilization-phase1-matrix.md) | Matrice stabilization phase 1 |

## Carte rapide

```
docs/
  [racine]            Docs generales + regles (.claude/rules/) + grading
  genai/              Infrastructure GenAI detaillee
  lean/               Prover iteration + endpoints
  parcours/           Guides pedagogiques (5 parcours)
  curriculum/         Stages curriculum
  analysis/           Analyses transverses
  research/           Recherches
  templates/          Templates
```

Pour la documentation principale du projet, voir [CLAUDE.md](../CLAUDE.md).
