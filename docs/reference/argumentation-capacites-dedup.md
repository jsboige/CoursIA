# Argumentation EPITA 2025 — deduplication et exposition licence

**Mesuré** sur `jsboigeEpita/2025-Epita-Intelligence-Symbolique` @ `e52042303d3a` (2026-11-14) via l'organe `scripts/research/argumentation_capacity_dedup.py dedup`.

Ce rapport est **reproductible** : il est calculé depuis le manifeste de capacités (`docs/reference/argumentation-capacities.json`) croisé à l'arbre réel du repo étudiant.

## 1. Capacités vendorisées (5)

Implantées à la fois dans la plateforme `argumentation_analysis/` **et** dans un projet étudiant numéroté — le projet est re-copié, pas appelé.

| Capacité | Origine(s) projet | Sous-arbres plateforme |
|---|---|---|
| JTMS / revision de croyances | 1.4.1-JTMS | argumentation_analysis/agents, argumentation_analysis/api, argumentation_analysis/plugins, argumentation_analysis/services |
| Detection de sophismes (symbolique + ML) | 2.3.2-detection-sophismes | argumentation_analysis/agents, argumentation_analysis/core, argumentation_analysis/plugins, argumentation_analysis/services |
| Contre-argument / debat dialogique | 2.3.3-generation-contre-argument, 1_2_7_argumentation_dialogique | argumentation_analysis/agents, argumentation_analysis/orchestration, argumentation_analysis/plugins |
| Gouvernance multi-agents | 2.1.6_multiagent_governance_prototype | argumentation_analysis/agents, argumentation_analysis/evaluation, argumentation_analysis/plugins |
| Logique formelle (Tweety via JPype) | 2.3.3-generation-contre-argument | argumentation_analysis/agents, argumentation_analysis/plugins |

## 2. Capacités écartelées (6)

Une même capacité s'étend sur ≥ 3 sous-arbres de la plateforme (coût d'extraction).

- **JTMS / revision de croyances** — 4 sous-arbres : argumentation_analysis/agents, argumentation_analysis/api, argumentation_analysis/plugins, argumentation_analysis/services
- **Argumentation Dung / AIF** — 4 sous-arbres : abs_arg_dung/agent.py, abs_arg_dung/aif_adapter.py, argumentation_analysis/orchestration, argumentation_analysis/plugins
- **Detection de sophismes (symbolique + ML)** — 4 sous-arbres : argumentation_analysis/agents, argumentation_analysis/core, argumentation_analysis/plugins, argumentation_analysis/services
- **Contre-argument / debat dialogique** — 3 sous-arbres : argumentation_analysis/agents, argumentation_analysis/orchestration, argumentation_analysis/plugins
- **Gouvernance multi-agents** — 3 sous-arbres : argumentation_analysis/agents, argumentation_analysis/evaluation, argumentation_analysis/plugins
- **Surfaces d'interaction** — 7 sous-arbres : CaseAI/index.html, api/agent_routes.py, api/auth.py, api/openapi.snapshot.json, apps/gradio_demo, interface_web/api, interface_web/app.py

## 3. Capacités multi-origines (1)

Produites par ≥ 2 projets étudiants (candidats d'extraction en boîte à outils partagée).

- **Contre-argument / debat dialogique** — 2.3.3-generation-contre-argument, 1_2_7_argumentation_dialogique

## 4. Modules dupliqués (18)

Un même fichier `.py` présent dans ≥ 3 dossiers (hors `__init__.py`).

- `app.py` × 5 : `2.3.6_local_llm/`, `apps/gradio_demo/`, `argumentation_analysis/services/web_api/`, `argumentation_analysis/ui/`, `interface_web/`
- `models.py` × 5 : `1_2_7_argumentation_dialogique/local_db_arg/src/core/`, `api/`, `argumentation_analysis/orchestration/`, `argumentation_analysis/reporting/`, `libs/mcp/client/`
- `main.py` × 5 : `1.4.1-JTMS/`, `1_2_7_argumentation_dialogique/local_db_arg/`, `api/`, `argumentation_analysis/api/`, `argumentation_analysis/services/mcp_server/`
- `strategies.py` × 5 : `2.3.3-generation-contre-argument/counter_agent/agent/`, `argumentation_analysis/agents/core/counter_argument/`, `argumentation_analysis/core/`, `argumentation_analysis/orchestration/`, `argumentation_analysis/pipelines/orchestration/execution/`
- `prompts.py` × 5 : `2.3.3-generation-contre-argument/counter_agent/llm/`, `argumentation_analysis/agents/core/extract/`, `argumentation_analysis/agents/core/informal/`, `argumentation_analysis/agents/core/pl/`, `argumentation_analysis/agents/templates/student_template/`
- `config.py` × 4 : `1_2_7_argumentation_dialogique/local_db_arg/src/interfaces/`, `abs_arg_dung/`, `argumentation_analysis/core/`, `argumentation_analysis/ui/`
- `conflict_resolution.py` × 3 : `2.1.6_multiagent_governance_prototype/governance/`, `argumentation_analysis/agents/core/governance/`, `argumentation_analysis/services/jtms/`
- `agent.py` × 3 : `2.3.5_argument_quality/src/`, `abs_arg_dung/`, `argumentation_analysis/agents/templates/student_template/`
- `cli.py` × 3 : `1_2_7_argumentation_dialogique/local_db_arg/src/interfaces/`, `2.1.6_multiagent_governance_prototype/`, `abs_arg_dung/`
- `utils.py` × 3 : `2.3.6_local_llm/local_llm/`, `argumentation_analysis/`, `argumentation_analysis/ui/`
- `manager.py` × 3 : `argumentation_analysis/orchestration/hierarchical/operational/`, `argumentation_analysis/orchestration/hierarchical/strategic/`, `argumentation_analysis/orchestration/hierarchical/tactical/`
- `unified_pipeline.py` × 3 : `argumentation_analysis/orchestration/`, `argumentation_analysis/pipelines/`, `argumentation_analysis/utils/`
- `plugin.py` × 3 : `argumentation_analysis/plugin_framework/core/plugins/standard/external_verification/`, `argumentation_analysis/plugin_framework/core/plugins/standard/taxonomy_explorer/`, `argumentation_analysis/plugins/analysis_tools/`
- `metrics.py` × 3 : `2.1.6_multiagent_governance_prototype/metrics/`, `2.3.3-generation-contre-argument/counter_agent/evaluation/`, `argumentation_analysis/agents/core/governance/`
- `reporting_utils.py` × 3 : `argumentation_analysis/core/utils/`, `argumentation_analysis/utils/`, `argumentation_analysis/utils/dev_tools/`
- `definitions.py` × 3 : `2.3.3-generation-contre-argument/counter_agent/agent/`, `argumentation_analysis/agents/core/counter_argument/`, `argumentation_analysis/agents/templates/student_template/`
- `state.py` × 3 : `argumentation_analysis/orchestration/hierarchical/operational/`, `argumentation_analysis/orchestration/hierarchical/strategic/`, `argumentation_analysis/orchestration/hierarchical/tactical/`
- `orchestrator.py` × 3 : `argumentation_analysis/orchestration/hierarchical/`, `argumentation_analysis/reporting/`, `argumentation_analysis/webapp/`

## 5. Exposition licence des binaires vendorisés

Binaires PE/JAR vendorisés dans le repo public. `licence` = **attribuée** (pas mesurée) ; `fichier de licence à côté` = **mesuré** à chaque passage.

| Famille | # binaires | avec fichier de licence |
|---|---|---|
| FOL prover | 8 | 0 |
| Java fat JAR | 1 | 0 |
| SAT solver | 3 | 0 |
| adaptateur | 1 | 0 |
| model finder | 1 | 0 |
| runtime | 2 | 0 |

**16 binaires vendorisés, dont 0 accompagnés d'un fichier de licence.**
