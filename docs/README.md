# Index de la documentation

Ce répertoire centralise la documentation projet déportée du CLAUDE.md. Chaque fichier documente un aspect précis du projet CoursIA (infrastructure, procédures, règles, état des séries).

## Référence (docs/reference/)

Documentation vivante, active et liée depuis CLAUDE.md / `.claude/rules/`.

| Fichier | Description |
|---------|-------------|
| [reference/common-commands.md](reference/common-commands.md) | Environnement, validation notebooks, scripts CLI |
| [reference/procedures-recurrentes.md](reference/procedures-recurrentes.md) | Workflow PR, dispatch, validation, pré-commit |
| [reference/architecture_mcp_roo.md](reference/architecture_mcp_roo.md) | Architecture des 34 outils MCP roo-state-manager |
| [reference/kernels-runtime.md](reference/kernels-runtime.md) | .NET, Python, WSL, conda envs |
| [reference/env-python-reparation.md](reference/env-python-reparation.md) | Réparation environnements Python |
| [reference/claude-code-config.md](reference/claude-code-config.md) | Agents, skills, rules, model selection |
| [reference/cluster-agents.md](reference/cluster-agents.md) | Machines cluster, GPU topology |
| [reference/teaching-context.md](reference/teaching-context.md) | Calendrier, scope EPITA-IS, agents par école |
| [reference/scripts-reference.md](reference/scripts-reference.md) | Catalogue scripts dépôt |
| [reference/subagents-reference.md](reference/subagents-reference.md) | Roster 21 agents + 17 skills |
| [reference/catalog_markers.md](reference/catalog_markers.md) | Marqueurs CATALOG-STATUS des READMEs (expansion + vérification CI) |
| [reference/audit-reassessment-findings.md](reference/audit-reassessment-findings.md) | Items d'audit automatisé déjà reclassés (protocole reassessment) |
| [reference/student-pr-template.md](reference/student-pr-template.md) | Template PR étudiante |
| [reference/readme-series-gabarit.md](reference/readme-series-gabarit.md) | Gabarit de référence des READMEs de séries (#2651) |

### Règles détaillées (docs/reference/)

| Fichier | Description |
|---------|-------------|
| [reference/pr-review-context.md](reference/pr-review-context.md) | Contexte incidents + anti-patterns reviews |
| [reference/proactive-coordination-detail.md](reference/proactive-coordination-detail.md) | Backlog 8 sources, mapping machines, cadence |
| [reference/regles-vigilance-detail.md](reference/regles-vigilance-detail.md) | Détails G.1-G.9 + incidents |
| [reference/regles-validation-detail.md](reference/regles-validation-detail.md) | Détails H.1-H.7 + incident Sudoku-13 |
| [reference/anti-regression-detail.md](reference/anti-regression-detail.md) | Patterns red-flag, protocole avant suppression |
| [reference/secrets-and-coord-detail.md](reference/secrets-and-coord-detail.md) | Secrets + coordination cross-machine |
| [reference/student-pr-reviews-detail.md](reference/student-pr-reviews-detail.md) | Incident, format public, workflow |
| [reference/user-blocker-signaling-detail.md](reference/user-blocker-signaling-detail.md) | Catégories + anti-patterns signaler |
| [reference/wsl-kernels-detail.md](reference/wsl-kernels-detail.md) | Détails WSL kernels |

### Outils & méthodologie (docs/reference/)

| Fichier | Description |
|---------|-------------|
| [reference/HEALTH_DASHBOARD.md](reference/HEALTH_DASHBOARD.md) | Tableau de santé du dépôt — snapshot dérivé du catalogue |
| [reference/accent-cure-defense-in-depth.md](reference/accent-cure-defense-in-depth.md) | Cure des accents FR & défense contre les régressions (#2876) |
| [reference/chatgpt-export-playwright.md](reference/chatgpt-export-playwright.md) | Explorer une longue conversation / un export ChatGPT via Playwright |
| [reference/dotnet-plotly-zero-restore.md](reference/dotnet-plotly-zero-restore.md) | Pattern .NET Interactive — figures Plotly « zero-restore » (technique C548-L2) |
| [reference/notebook-formatting.md](reference/notebook-formatting.md) | Mise en forme visuelle des notebooks — directives + vérification de rendu |
| [reference/notebook-parity-table.md](reference/notebook-parity-table.md) | Table de parité cross-série — notebooks Python ⇄ .NET |
| [reference/stale-tree-drift-scan.md](reference/stale-tree-drift-scan.md) | Scan de drift sur worktree frais (anti-phantom) |

## GenAI (docs/genai/)

Documentation détaillée de l'infrastructure GenAI (ComfyUI, Docker, modèles locaux).

| Fichier | Description |
|---------|-------------|
| [genai/genai-services.md](genai/genai-services.md) | Architectures Qwen/Lumina, mapping notebooks |
| [genai/audio-embed-pattern.md](genai/audio-embed-pattern.md) | Pattern d'embed audio GenAI + leçons de réparation |
| [genai/auth-flip-runbook.md](genai/auth-flip-runbook.md) | Runbook — flip d'authentification des services exposés (#16 P2) |
| [genai/open-webui-orchestration.md](genai/open-webui-orchestration.md) | Orchestration et tâches planifiées avec Open WebUI v0.9.0 |
| [genai/secrets-management.md](genai/secrets-management.md) | Secrets management — central source of truth (master.env + render_envs.py) |
| [genai/service-security-audit.md](genai/service-security-audit.md) | Audit de sécurisation des services IA auto-hébergés (po-2023) |

## QuantConnect (docs/qc/)

| Fichier | Description |
|---------|-------------|
| [qc/quantconnect.md](qc/quantconnect.md) | Backtests, structure, livre référence |
| [qc/qc-comparative-backtests.md](qc/qc-comparative-backtests.md) | Baselines alignées + analyse comparative backtests (#1630) |
| [qc/qc-batch-methodology-playbook.md](qc/qc-batch-methodology-playbook.md) | Playbook méthodologie batch QC (#1621) |
| [qc/qc-strategies-status.md](qc/qc-strategies-status.md) | Statut des stratégies QuantConnect — source de vérité |

## Lean (docs/lean/)

Iteration history prover, intractable diagnosis, LLM endpoints.

| Fichier | Description |
|---------|-------------|
| [lean/coordinator-workflow.md](lean/coordinator-workflow.md) | Disciplines coordinateur Lean (build pre-merge, itération prover) |
| [lean/llm-endpoints.md](lean/llm-endpoints.md) | Providers LLM du prover multi-agent (configuration, sans clés) |
| [lean/prover_iteration_history.md](lean/prover_iteration_history.md) | Historique itération prover |
| [lean/sota-2026-analysis.md](lean/sota-2026-analysis.md) | État de l'art preuve automatique Lean 4 (mai 2026) |
| [lean/ab-methodology.md](lean/ab-methodology.md) | Méthodologie d'A/B pour le harnais prover Lean |
| [lean/i18n-inventory-cycle-38.md](lean/i18n-inventory-cycle-38.md) | Lean i18n — inventaire FR/EN et proposition de convention (cycle 38, See #4980) |
| [lean/i18n-sibling-patterns.md](lean/i18n-sibling-patterns.md) | Lean i18n — patterns de paires FR/EN et discipline du checker (#4980) |
| [lean/stable_marriage_intractable_diagnosis.md](archive/lean-intractable-diagnosis/stable-marriage.md) | Diagnostic des preuves stable-marriage intractables (archivé c.696) |

## Curriculum (docs/curriculum/)

Guides pédagogiques et parcours d'apprentissage.

| Fichier | Description |
|---------|-------------|
| [curriculum/ia-classique.md](curriculum/ia-classique.md) | Parcours IA classique (recherche, CSP, Sudoku) |
| [curriculum/ia-symbolique.md](curriculum/ia-symbolique.md) | Parcours IA symbolique (Lean, Tweety, SemanticWeb, Planning) |
| [curriculum/recherche.md](curriculum/recherche.md) | Parcours recherche avancée (Infer.NET, Pyro, IIT, RL, GameTheory) |
| [curriculum/trading.md](curriculum/trading.md) | Parcours trading algorithmique (QuantConnect, ML, Probas) |
| [curriculum/genai.md](curriculum/genai.md) | Parcours GenAI multimodale (Image, Audio, Vidéo, Texte) |
| [curriculum/stage5_mamba_ssm.md](curriculum/stage5_mamba_ssm.md) | Note d'exploration Mamba/SSM pour le forecasting financier |

## Lecture transversale

| Fichier | Description |
|---------|-------------|
| [grothendieckian-lens.md](grothendieckian-lens.md) | Clé de lecture grothendieckienne du dépôt (changement de représentation, certification A/B/C) |

## Internationalisation & Traduction (docs/i18n/, docs/translation/)

Infrastructure de synchronisation et moteur de traduction du dépôt (EPIC #4957, #6949, parent #1650).

| Fichier | Description |
|---------|-------------|
| [i18n/CSV-by-series-design.md](i18n/CSV-by-series-design.md) | Design doc infra CSV-by-series (EPIC #4957 Phase 1) |
| [i18n/argumentum-fork-mapping.md](i18n/argumentum-fork-mapping.md) | Cartographie fork Argumentum → CoursIA (EPIC #6949 T3) |
| [translation/argumentum-fork-mapping.md](translation/argumentum-fork-mapping.md) | Référence pérenne couche T3 (moteur `translate_csv.py`, #6949/#6976) |
| [translation/epic-4957-status.md](translation/epic-4957-status.md) | État de clôture Phase 1 infra traduction (#4957 → #1650) |

## ICT (docs/ict/)

Synthèses transversales de la série IIT → ICT (Epic #4588, grade C-documentaire).

| Fichier | Description |
|---------|-------------|
| [ict/synthese-invariants-dissociations-obstructions.md](ict/synthese-invariants-dissociations-obstructions.md) | Grille 3 régimes de lecture d'une trajectoire (#7399, #4588) |

## Ledgers cumulatifs (docs/ledgers/)

Tables d'audit cumulatives par Epic (mandat user, format longue durée).

| Fichier | Description |
|---------|-------------|
| [ledgers/3801-sota-axe2.md](ledgers/3801-sota-axe2.md) | Ledger axe-2 SOTA par famille, 5 verdicts (EPIC #3801) |

## Suivis de cycle (docs/suivis/)

Notes de suivi de cycle par série (transitions architecturales et narratives).

| Fichier | Description |
|---------|-------------|
| [suivis/iit-ict-transition.md](suivis/iit-ict-transition.md) | Transition IIT → ICT, pivot série ICT-Series (#4588, #5081) |

## Archive (docs/archive/)

Documents conservés pour référence mais inactifs. Index complet : [archive/INDEX.md](archive/INDEX.md).

| Fichier | Description |
|---------|-------------|
| [archive/ml-trading-state.md](archive/ml-trading-state.md) | État ML trading (historique) |
| [archive/visitor-navigation-guide.md](archive/visitor-navigation-guide.md) | Carte du visiteur |
| [archive/research/dl_predictability_finance_2026.md](archive/research/dl_predictability_finance_2026.md) | Prédictibilité DL finance 2026 |
| [archive/analysis/qc-notebooks-exec-classification.md](archive/analysis/qc-notebooks-exec-classification.md) | Classification exécution notebooks QC |

**Sous-répertoires archives** :

- [archive/investigation-mcp-nuget/](archive/investigation-mcp-nuget/INDEX.md) — Investigation MCP Jupyter / NuGet (26 fichiers)
- [archive/genai/](archive/genai/README.md) — Infrastructure GenAI détaillée (16 fichiers)
- [archive/suivis/genai-image/](archive/suivis/genai-image/INDEX.md) — Suivi ComfyUI/Qwen (8 fichiers + 4 phases)

## Carte rapide

```
docs/
  reference/         Docs vivantes liées depuis CLAUDE.md / rules
  genai/             Infrastructure GenAI
  qc/                QuantConnect reference
  lean/              Prover itération + endpoints
  curriculum/        Parcours pédagogiques + stages
  i18n/              Infrastructure i18n CSV-by-series (#4957, #6949)
  translation/       Moteur de traduction T3 + état Epic (#6949, #4957)
  ict/               Synthèses transversales IIT → ICT (#4588)
  ledgers/           Ledgers d'audit cumulatifs par Epic (#3801)
  suivis/            Suivis de cycle (transitions de série)
  grothendieckian-lens.md  Clé de lecture transversale du dépôt
  archive/           Documents inactifs (ex-_archives)
```

Pour la vue d'ensemble pédagogique du dépôt, voir le [README principal](../README.md) ; pour les instructions de travail des agents, [CLAUDE.md](../CLAUDE.md).
