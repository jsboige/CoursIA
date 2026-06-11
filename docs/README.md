# Index de la documentation

Ce repertoire centralise la documentation projet deportee du CLAUDE.md. Chaque fichier documente un aspect precis du projet CoursIA (infrastructure, procedures, regles, etat des series).

## Reference (docs/reference/)

Documentation vivante, active et liee depuis CLAUDE.md / `.claude/rules/`.

| Fichier | Description |
|---------|-------------|
| [reference/common-commands.md](reference/common-commands.md) | Environnement, validation notebooks, scripts CLI |
| [reference/procedures-recurrentes.md](reference/procedures-recurrentes.md) | Workflow PR, dispatch, validation, pre-commit |
| [reference/architecture_mcp_roo.md](reference/architecture_mcp_roo.md) | Architecture des 34 outils MCP roo-state-manager |
| [reference/kernels-runtime.md](reference/kernels-runtime.md) | .NET, Python, WSL, conda envs |
| [reference/env-python-reparation.md](reference/env-python-reparation.md) | Reparation environnements Python |
| [reference/claude-code-config.md](reference/claude-code-config.md) | Agents, skills, rules, model selection |
| [reference/cluster-agents.md](reference/cluster-agents.md) | Machines cluster, GPU topology |
| [reference/teaching-context.md](reference/teaching-context.md) | Calendrier, scope EPITA-IS, agents par ecole |
| [reference/scripts-reference.md](reference/scripts-reference.md) | Catalogue scripts depot |
| [reference/subagents-reference.md](reference/subagents-reference.md) | Roster 21 agents + 15 skills |
| [reference/ece-grading.md](reference/ece-grading.md) | Pipeline GradeBookApp (EPITA-ECE) |
| [reference/esgf-grading.md](reference/esgf-grading.md) | Pipeline ESGF (cohorte ESGF, calibration) |
| [reference/catalog_markers.md](reference/catalog_markers.md) | Marqueurs CATALOG-STATUS des READMEs (expansion + verification CI) |
| [reference/audit-reassessment-findings.md](reference/audit-reassessment-findings.md) | Items d'audit automatise deja reclasses (protocole reassessment) |
| [reference/student-pr-template.md](reference/student-pr-template.md) | Template PR etudiante |
| [reference/readme-series-gabarit.md](reference/readme-series-gabarit.md) | Gabarit de reference des READMEs de series (#2651) |

### Regles detaillees (docs/reference/)

| Fichier | Description |
|---------|-------------|
| [reference/pr-review-context.md](reference/pr-review-context.md) | Contexte incidents + anti-patterns reviews |
| [reference/proactive-coordination-detail.md](reference/proactive-coordination-detail.md) | Backlog 8 sources, mapping machines, cadence |
| [reference/regles-vigilance-detail.md](reference/regles-vigilance-detail.md) | Details G.1-G.9 + incidents |
| [reference/regles-validation-detail.md](reference/regles-validation-detail.md) | Details H.1-H.7 + incident Sudoku-13 |
| [reference/anti-regression-detail.md](reference/anti-regression-detail.md) | Patterns red-flag, protocole avant suppression |
| [reference/secrets-and-coord-detail.md](reference/secrets-and-coord-detail.md) | Secrets + coordination cross-machine |
| [reference/student-pr-reviews-detail.md](reference/student-pr-reviews-detail.md) | Incident, format public, workflow |
| [reference/user-blocker-signaling-detail.md](reference/user-blocker-signaling-detail.md) | Categories + anti-patterns signaler |
| [reference/wsl-kernels-detail.md](reference/wsl-kernels-detail.md) | Details WSL kernels |

## GenAI (docs/genai/)

Documentation detaillee de l'infrastructure GenAI (ComfyUI, Docker, modeles locaux).

| Fichier | Description |
|---------|-------------|
| [genai/genai-services.md](genai/genai-services.md) | Architectures Qwen/Lumina, mapping notebooks |

## QuantConnect (docs/qc/)

| Fichier | Description |
|---------|-------------|
| [qc/quantconnect.md](qc/quantconnect.md) | Backtests, structure, livre reference |
| [qc/qc-comparative-backtests.md](qc/qc-comparative-backtests.md) | Baselines alignees + analyse comparative backtests (#1630) |

## Lean (docs/lean/)

Iteration history prover, intractable diagnosis, LLM endpoints.

| Fichier | Description |
|---------|-------------|
| [lean/coordinator-workflow.md](lean/coordinator-workflow.md) | Disciplines coordinateur Lean (build pre-merge, iteration prover) |
| [lean/llm-endpoints.md](lean/llm-endpoints.md) | Providers LLM du prover multi-agent (configuration, sans cles) |
| [lean/prover_iteration_history.md](lean/prover_iteration_history.md) | Historique iteration prover |
| [lean/sota-2026-analysis.md](lean/sota-2026-analysis.md) | Etat de l'art preuve automatique Lean 4 (mai 2026) |
| [lean/stable_marriage_intractable_diagnosis.md](lean/stable_marriage_intractable_diagnosis.md) | Diagnostic des preuves stable-marriage intractables |

## Curriculum (docs/curriculum/)

Guides pedagogiques et parcours d'apprentissage.

| Fichier | Description |
|---------|-------------|
| [curriculum/ia-classique.md](curriculum/ia-classique.md) | Parcours IA classique (recherche, CSP, Sudoku) |
| [curriculum/ia-symbolique.md](curriculum/ia-symbolique.md) | Parcours IA symbolique (Lean, Tweety, SemanticWeb, Planning) |
| [curriculum/recherche.md](curriculum/recherche.md) | Parcours recherche avancee (Infer.NET, Pyro, IIT, RL, GameTheory) |
| [curriculum/trading.md](curriculum/trading.md) | Parcours trading algorithmique (QuantConnect, ML, Probas) |
| [curriculum/genai.md](curriculum/genai.md) | Parcours GenAI multimodale (Image, Audio, Video, Texte) |
| [curriculum/stage5_mamba_ssm.md](curriculum/stage5_mamba_ssm.md) | Note d'exploration Mamba/SSM pour le forecasting financier |

## Lecture transversale

| Fichier | Description |
|---------|-------------|
| [grothendieckian-lens.md](grothendieckian-lens.md) | Cle de lecture grothendieckienne du depot (changement de representation, certification A/B/C) |

## Archive (docs/archive/)

Documents conserves pour reference mais inactifs. Index complet : [archive/INDEX.md](archive/INDEX.md).

| Fichier | Description |
|---------|-------------|
| [archive/ml-trading-state.md](archive/ml-trading-state.md) | Etat ML trading (historique) |
| [archive/visitor-navigation-guide.md](archive/visitor-navigation-guide.md) | Carte du visiteur |
| [archive/research/dl_predictability_finance_2026.md](archive/research/dl_predictability_finance_2026.md) | Predictibilite DL finance 2026 |
| [archive/analysis/qc-notebooks-exec-classification.md](archive/analysis/qc-notebooks-exec-classification.md) | Classification execution notebooks QC |

**Sous-repertoires archives** :

- [archive/investigation-mcp-nuget/](archive/investigation-mcp-nuget/INDEX.md) — Investigation MCP Jupyter / NuGet (26 fichiers)
- [archive/genai/](archive/genai/README.md) — Infrastructure GenAI detaillee (13+ fichiers)
- [archive/suivis/genai-image/](archive/suivis/genai-image/INDEX.md) — Suivi ComfyUI/Qwen (8 fichiers + 4 phases)

## Carte rapide

```
docs/
  reference/         Docs vivantes liees depuis CLAUDE.md / rules
  genai/             Infrastructure GenAI
  qc/                QuantConnect reference
  lean/              Prover iteration + endpoints
  curriculum/        Parcours pedagogiques + stages
  grothendieckian-lens.md  Cle de lecture transversale du depot
  archive/           Documents inactifs (ex-_archives)
```

Pour la vue d'ensemble pedagogique du depot, voir le [README principal](../README.md) ; pour les instructions de travail des agents, [CLAUDE.md](../CLAUDE.md).
