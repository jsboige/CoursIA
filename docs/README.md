# Index de la documentation

Ce répertoire centralise la documentation projet déportée du CLAUDE.md. Chaque fichier documente un aspect précis du projet CoursIA (infrastructure, procédures, règles, état des séries).

## Racine (docs/)

Fichiers présents directement à la racine du répertoire `docs/`. Triage initial #7422 (c.805, po-2024 — audité par lecture disque + cross-check liens).

| Fichier | Verdict | Raison |
|---------|---------|--------|
| [README.md](README.md) (ce fichier) | **KEEP** | Index vivant — 58 liens internes vérifiés c.805 (aucun mort), 11 sections cohérentes avec disque, organisation par catégorie stable |
| [index.qmd](index.qmd) | **KEEP + repair** | Portail Quarto miroir du `index.md` racine — 3 liens cassés détectés (lean/README.md → lean/coordinator-workflow.md ; ../parcours.qmd → ../../parcours.qmd ; ../COURSE_CATALOG.generated.md → ../../COURSE_CATALOG.generated.md) — corrigés c.805 |
| [grothendieckian-lens.md](grothendieckian-lens.md) | **KEEP** | Manifesto pédagogique transversal (116 lignes), durable, lié depuis `index.md` racine + docs/README.md ; aucune rot détectée |
| [PARCOURS.md](PARCOURS.md) | **KEEP** | Schéma maturité 3 axes (éditorial / reproductibilité / revue scientifique) — décompose le `maturity` monolithique du catalogue (5 valeurs mélangées) en 3 préoccupations orthogonales auditables indépendamment. ACCEPTÉ 2026-07-23, pilote c.763 critères 1-3. Linked #8051. 110 lignes. Triage #7422 (c.911, po-2023) |

## Référence (docs/reference/)

Documentation vivante, active et liée depuis CLAUDE.md / `.claude/rules/`.

| Fichier | Description |
|---------|-------------|
| [reference/common-commands.md](reference/common-commands.md) | Environnement, validation notebooks, scripts CLI |
| [reference/procedures-recurrentes.md](reference/procedures-recurrentes.md) | Workflow PR, dispatch, validation, pré-commit |
| [reference/architecture_mcp_roo.md](reference/architecture_mcp_roo.md) | Cycle de vie, logs et diagnostic des serveurs MCP (l'inventaire des 15 outils roo-state-manager vit en amont : [HARNESS-OVERVIEW.md](https://github.com/jsboige/roo-extensions/blob/main/docs/harness/HARNESS-OVERVIEW.md) §2) |
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
| [reference/lean-axiom-coverage.md](reference/lean-axiom-coverage.md) | Couverture axiomes du gate proof-integrity par lake (22 lakes inventoriés, 2 câblés en CI : `lean-knot.yml` + `lean-conway.yml`) — classes dangereuses `native_decide.*`/`sorryAx`/`Classical.choice`. Détail de référence pour §B.3 de `.claude/rules/pr-review-discipline.md`. Établi cycle c.950 (worker po-2023, lane `myia-po-2023:CoursIA-2`), 167 lignes. See #8738 (step 3), #8752 (livraison) |
| [reference/secrets-and-coord-detail.md](reference/secrets-and-coord-detail.md) | Secrets + coordination cross-machine |
| [reference/student-pr-reviews-detail.md](reference/student-pr-reviews-detail.md) | Incident, format public, workflow |
| [reference/user-blocker-signaling-detail.md](reference/user-blocker-signaling-detail.md) | Catégories + anti-patterns signaler |
| [reference/wsl-kernels-detail.md](reference/wsl-kernels-detail.md) | Détails WSL kernels |

### Outils & méthodologie (docs/reference/)

| Fichier | Description |
|---------|-------------|
| [archive/reference/HEALTH_DASHBOARD.md](archive/reference/HEALTH_DASHBOARD.md) | **Archivé 2026-08-08** (était [reference/](reference/)) : Tableau de santé du dépôt — snapshot statique auto-généré depuis `COURSE_CATALOG.generated.json` (acceptance #4 de #4210). **Record historique** — superseded pour usage live par le marqueur `CATALOG-STATUS` dans chaque README de série (cron `catalog-cron.yml` quotidien). 77 lignes. Linked #4210 |
| [reference/accent-cure-defense-in-depth.md](reference/accent-cure-defense-in-depth.md) | Cure des accents FR & défense contre les régressions (#2876) |
| [reference/chatgpt-export-playwright.md](reference/chatgpt-export-playwright.md) | Explorer une longue conversation / un export ChatGPT via Playwright |
| [reference/dotnet-plotly-zero-restore.md](reference/dotnet-plotly-zero-restore.md) | Pattern .NET Interactive — figures Plotly « zero-restore » (technique C548-L2) |
| [reference/notebook-formatting.md](reference/notebook-formatting.md) | Mise en forme visuelle des notebooks — directives + vérification de rendu |
| [reference/notebook-parity-table.md](reference/notebook-parity-table.md) | Table de parité cross-série — notebooks Python ⇄ .NET |
| [reference/notebook-counts-reconciliation.md](reference/notebook-counts-reconciliation.md) | Réconciliation forensic des 4 sources de comptage notebooks (disque 946 / forensic 944 / catalogue 830 / STABLE_SNAPSHOT 934) — écart catalogue-disque = 116 = 84 drift + 30 exclusions par design, filtre `scripts/audit/check_denominators.py`. SHA daté 2026-07-23. 174 lignes. Linked #8050 |
| [reference/stale-tree-drift-scan.md](reference/stale-tree-drift-scan.md) | Scan de drift sur worktree frais (anti-phantom) |
| [reference/orphan-branch-scan-l576.md](reference/orphan-branch-scan-l576.md) | Scan de branche orpheline (L576 ★★) — compound gate 3 ancres (`merge-base` + REST `commits/<sha>/pulls` + `gh pr list --search head:<branch>`) anti-FPOS du REST, decision matrix 5 lignes. Détail de référence pour la section « Orphan-branch scan » de `.claude/rules/git-workflow.md`. 105 lignes. Origine : investigation 5 branches `jsboige/*` attachées à #7086-#7091 (c.576) |

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
| [reference/mbml-source-attribution.md](reference/mbml-source-attribution.md) | Attribution de source MBML/Infer.NET — table de correspondance notebook ↔ source canonique pour la série Probas/ (36 notebooks Infer + PyMC + 2 racine vs *MBML Book* Herbrich + TrueSkill 2007 + WinBUGS/JAGS). Établie audit distillation #8081 (c.803, 2026-07-23). Les 4 sous-items de backfill/archivage extraits en issues filles #8702-#8705. Réqualification #7422 (déplacement audit/ → reference/, retrait des verdicts/décisions de cycle). |

> Note : `lean/stable_marriage_intractable_diagnosis.md` a été déplacé vers [archive/lean-intractable-diagnosis/stable-marriage.md](archive/lean-intractable-diagnosis/stable-marriage.md) (archivé c.696).

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

## Métadonnées notebooks (docs/notebook-metadata/)

Schémas canoniques de métadonnées par notebook : registre datasets (licence + checksum), matrice coût/ressource, et registre de revues éditoriales tierces. Consommés par `scripts/audit/check_*.py` et liés depuis `THIRD_PARTY_NOTICES.md`. Triage #7422 (c.839, po-2023 — slice `notebook-metadata/` non couverte par c.549/c.557/c.600/c.705/c.715/c.728n/c.728r/c.728s/c.734/c.728y+36/c.728y+37).

| Fichier | Verdict | Raison |
|---------|---------|--------|
| [notebook-metadata/DATASET_REGISTRY.md](notebook-metadata/DATASET_REGISTRY.md) | **KEEP** | Registre canonique datasets (~25 fichiers, 9 familles) avec licence + checksum SHA256 — alimenté par `scripts/audit/check_dataset_registry.py --audit` ; lié depuis [THIRD_PARTY_NOTICES.md §0](../THIRD_PARTY_NOTICES.md) (séparation licences code vs datasets). Issue #8055 tranche 2 (V0 pilote c.795). 210 lignes |
| [notebook-metadata/DATASET_CARD.md](notebook-metadata/DATASET_CARD.md) | **KEEP** | Template grade B-méthodologique pour dataset sensible (caractère synthétique + périmètre RGPD + procédure re-validation sur fork). Complète `DATASET_REGISTRY.md` avec une couche descriptive par dataset. Issue #8055 tranche 2. 154 lignes |
| [notebook-metadata/cost-matrix.md](notebook-metadata/cost-matrix.md) | **KEEP** | Schéma `cost:` frontmatter portable (api_usd_est / cpu_min / gpu_min / vram_gb / qc_cloud_required) — pilote V0 c.794, issue #8056. Consommé par `scripts/audit/check_cost_metadata.py` ; intégration audit sémantique #8052. 375 lignes — référence opérationnelle majeure |
| [notebook-metadata/EDITORIAL_REVIEW_CARD.md](notebook-metadata/EDITORIAL_REVIEW_CARD.md) | **KEEP** | Template canonique c.764 — copié/adapté par chaque reviewer pour ajouter une entrée à `editorial-review-registry.md`. 5 portées : typo / factual / pedagogie / substance / full (seules `factual`/`substance`/`full` permettent promotion `BETA → FINAL`, cf `docs/PARCOURS.md` §Axe 1). 93 lignes |
| [notebook-metadata/editorial-review-registry.md](notebook-metadata/editorial-review-registry.md) | **KEEP** | Pilote fondateur c.764 (phase 2 issue #8051 critère #4) — registre whitelist YAML curé manuellement des revues éditoriales tierces. Sans signal `editorial_reviewed_by` non-null dans ce registre, `classify_editorial()` n'émet jamais `FINAL` (598 entrées historiques rétrogradées par défaut, design anti-auto-promotion). Consommé par `scripts/audit/check_editorial_review.py`. 179 lignes |

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

## Audit sémantique cross-famille (docs/audit/)

Cadrage **méthodologique** de l'audit sémantique (grade B-méthodologique, EPIC #4208 + #8052). Les **comptes-rendus** de cycle et les **findings** ne vivent pas ici : dashboard RooSync pour l'éphémère, issue GitHub pour l'actionnable (règle HARD [audit-cross-source-distillation.md](../.claude/rules/audit-cross-source-distillation.md)).

| Fichier | Description |
|---------|-------------|
| [audit/sampling-protocol.md](audit/sampling-protocol.md) | Protocole d'audit d'échantillonnage sémantique cross-famille : ≥5%/famille par cycle mensuel, env-vierge (pas cache), confrontation claims-markdown ↔ sorties réelles, détection fallback silencieux (TenSEAL CKKS incident fondateur). 5 litmus + grille outillée `scripts/audit/extract_claims_vs_outputs.py`, avec état de validation par litmus (2/5 jamais déclenchés) et limite connue du matching numérique. Grade B-méthodologique, #8052. 164 lignes |

## ICT (docs/ict/)

Synthèses transversales de la série IIT → ICT (Epic #4588, grade C-documentaire).

| Fichier | Description |
|---------|-------------|
| [ict/synthese-invariants-dissociations-obstructions.md](ict/synthese-invariants-dissociations-obstructions.md) | Grille 3 régimes de lecture d'une trajectoire (#7399, #4588) |
| [ict/dissociations-matrix.md](ict/dissociations-matrix.md) | Matrice canonique `notebook × claim × proxy × contrôle × seeds × verdict × portée` (grade C-documentaire, #7734, #4588) |
| [ict/cadrage-trajectoires-representations.md](ict/cadrage-trajectoires-representations.md) | Cadrage « trajectoires de représentations » — pivot états → représentations (échelle LLM, strate 5). Grade C-documentaire, livrable N2 de #7396, See #4588. 169 lignes |
| [ict/genealogy-representation-interne.md](ict/genealogy-representation-interne.md) | 4ᵉ fil de lecture ICT — généalogie backward de `p̂` (ICT-10 → ICT-17), 6 maillons diachroniques. Grade C-documentaire, #7735 + Part of #7396, See #4588. 96 lignes |

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
  audit/             Audit sémantique cross-famille (sampling-protocol + history/) — #8052
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
  PARCOURS.md        Schéma maturité 3 axes (éditorial / reproductibilité / revue) — #8051
  archive/           Documents inactifs (ex-_archives)
```

Pour la vue d'ensemble pédagogique du dépôt, voir le [README principal](../README.md) ; pour les instructions de travail des agents, [CLAUDE.md](../CLAUDE.md).
