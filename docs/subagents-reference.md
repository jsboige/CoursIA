# Sous-agents spécialistes — référence + mandat d'usage side-tracks

Les 21 sous-agents définis dans [.claude/agents/](../.claude/agents/) sont des **spécialistes** invoquables via l'outil `Agent` (`subagent_type: "<nom>"`). Plusieurs sont **orientés side-tracks long-cours** : ils peuvent être lancés en **asynchrone** (`run_in_background: true`) pour faire avancer une Epic side-track pendant que le worker interactif tient sa track principale sur wakeup horaire.

**3 spécialistes side-track créés 2026-05-23** (corollaire du mandat Epics) : `prover-forensic` (#1453, comble le GAP prover), `training-specialist` + skill `train-model` (#1454), `genai-iterator` + skill `genai-iterate` (#1385). Chacun encode les artefacts réels du dépôt (pipeline, CLI, configs) — voir leur fiche.

**Mandat (mandat user 2026-05-23)** : les Epics side-tracks DOIVENT déléguer aux sous-agents spécialistes async quand un specialist existe. Ne pas refaire à la main ce qu'un specialist fait mieux. Voir [.claude/rules/proactive-coordination.md](../.claude/rules/proactive-coordination.md).

## Orchestrateurs persistants — idéaux pour side-tracks async

| Agent | Rôle | Pourquoi side-track |
|-------|------|---------------------|
| `series-improver` | Orchestre l'amélioration itérative d'une **série** de notebooks, **suivi de progression persistant + reprise après redémarrage VSCode** | Batch long-cours qui survit aux interruptions — le driver async par excellence |
| `notebook-iterative-builder` | Orchestre les cycles création/amélioration d'**un** notebook (design → execute → validate → enrich → fix) jusqu'à convergence qualité | Travail profond multi-étapes sur un notebook complexe (nouvelles séries) |
| `training-specialist` | Orchestre l'entraînement ML (RL/PPO, Decision Transformer, LSTM, transformer, mamba, PatchTST, MoE, GNN), thermal-safe GPU + walk-forward/multi-seed/DM + registry | **#1454** Training & Post-Training — runs GPU longs en BG pendant la main track |
| `genai-iterator` | Itère sur les notebooks GenAI contre la stack auto-hébergée (ComfyUI/Qwen, Forge, vLLM) via le CLI genai-stack : auth, sous-domaines, quantization, GPU/VRAM | **#1385** GenAI series + hosting — itération batch async |
| `prover-forensic` | **Read-only** forensic des traces du harness prover Lean (mappe pathologies → code, propose deltas bornés ROI-rankés) | **#1453** harness co-evolution — survey async pendant les BG iter prover |

Distinction : `series-improver` = grain **série** (batch + resume) ; `notebook-iterative-builder` = grain **notebook** (convergence profonde). Complémentaires, pas redondants.

## Mapping side-track Epic → sous-agents mandatés

### #1454 Training & Post-Training (po-2024 ⇄ ai-01)
- **Training ML** : `training-specialist` (orchestrateur thermal-safe + walk-forward/multi-seed/DM, skill `/train-model`) — driver async de l'Epic. Encode `ML-Training-Pipeline/` (REGISTRY/CURRICULUM, 30+ `train_*.py`, watchdog thermique MAX_TEMP=80C `cool_sleep`).
- **Trading** : `qc-strategy-analyzer` (diag BROKEN/NEEDS_IMPROVEMENT), `qc-strategy-improver` (workflow amélioration complet), `qc-robustness-researcher` (walk-forward multi-régime), `qc-research-notebook` (idéation/exploration avant implémentation).
- **Nouvelles séries RL/PPO + GenAI fine-tuning/LoRA** : `notebook-designer` (création from scratch) + `notebook-iterative-builder` (convergence qualité).

### GenAI series #1385 (po-2023 side-track + tests GenAI ai-01)
- **Driver** : `genai-iterator` (orchestre l'itération contre la stack via CLI genai-stack, skill `/genai-iterate`) — auth/sous-domaines/quantization/GPU.
- `notebook-modernizer` (libs/APIs obsolètes via recherche web), `notebook-executor` (exécution + capture outputs via MCP Jupyter), `notebook-validator` (validation structure/exec/pédagogie).
- `infer-notebook-enricher` pour la famille Probas/Infer.NET.

### #1455 TP EPITA → exemples guidés + nouveaux exercices (po-2025) + modernisation #999
- `series-improver` (batch + resume sur la série), `notebook-cleaner` (markdown pédagogique : dédup, hiérarchie), `notebook-enricher` (interprétations/transitions), `notebook-designer` (nouveaux exercices à la suite), `notebook-cell-iterator` (correction ciblée d'une cellule), `notebook-validator` (vérif finale).
- Respecter [.claude/rules/exercise-example-labeling.md](../.claude/rules/exercise-example-labeling.md) (content-based, jamais de find-replace aveugle).

### #1453 Prover harness co-evolution (po-2026 ⇄ ai-01)
- **`prover-forensic`** (créé 2026-05-23, comble l'ancien GAP) : forensic **read-only** des traces (`agent_tests/prover/traces/*_result.json`, `baselines/traces/*.spans.jsonl`) → macro-signal + pathologie ancre + cause racine + deltas ROI-rankés bornés par les traces. Aucune édition `.lean`/harness. Lancer en async pendant les BG iter prover ; la proposition P1 est implémentée par po-2026 sur sa main track, ai-01 valide via re-run.

### Cross-cutting maintenance (toutes machines, alignement env)
- `readme-hierarchy-auditor` (audit/maj hiérarchie README bottom-up), `readme-updater` (maj README d'une série après ajout/modif notebooks).
- `slide-analyzer` / `slide-improver` (decks PPTX/Marp, vision sk-agent) pour les tracks slides EPITA/ECE.
- `code-explorer` (read-only), `general-purpose` (catch-all) pour exploration/analyse async non couverte par un specialist.

## Usage async (pattern)

```
Agent(
  subagent_type: "series-improver",     # ou notebook-modernizer, qc-strategy-improver, etc.
  run_in_background: true,              # side-track async pendant la main track
  description: "<3-5 mots>",
  prompt: "<contexte repo + Epic + livrable attendu + contraintes (read-only si analyse, outputs réels, anti-regression)>"
)
```

Le message final du sous-agent revient en notification. Les sous-agents read-only (analyse) ne risquent pas de collision ; pour les sous-agents qui éditent, **un seul à la fois par notebook/série** (pas d'enrichissement parallèle du même fichier — règle CLAUDE.md).

## Skills `.claude/skills/` — slash-commands mandatés

15 skills invoquables en slash-command (`/<nom>`). Là où un skill couvre une tâche récurrente, **l'utiliser plutôt que de réimproviser le workflow** (mandat user 2026-05-23 : catalogue clair pour encourager l'usage).

### Workflows actionnables (slash-commands)

| Skill | Quand l'utiliser | Track / Epic |
|-------|------------------|--------------|
| `/coordinate` | Reprise session coordination (mémoire + RooSync + issues → briefing + dispatch). `--dispatch`, `--focus`, `--reply-all` | ai-01 chaque wakeup |
| `/review-student-prs` | **Recycler les TP étudiants** : review + exécution + merge intelligent (exercice résolu → exemple + nouvel exercice à la suite). `--class`, `--timeslot`, `--dry-run` | EPITA-IS / ECE / PrCon, #1455 |
| `/build-notebook` | Créer/améliorer/corriger un notebook avec scoring qualité itératif (`new\|improve\|fix`) | nouvelles séries (#1454 RL/PPO, GenAI) |
| `/enrich-notebooks` | Markdown pédagogique (interprétations, transitions). `--execute`, `--fix-errors`, `--iterate` | #1455, GenAI |
| `/cleanup-notebooks` | Réorganiser markdown enrichi (dédup, hiérarchie). `--hierarchy-only` | post-enrichissement |
| `/execute-notebook` | Exécution (scripts locaux ou MCP Jupyter). `--mode`, `--batch`, `--save` | validation toutes séries |
| `/verify-notebooks` | Vérif + fix itératif (`--quick`, `--fix`, `--python-only`, `--dotnet-only`) | gate avant PR |
| `/validate-genai` | Valider stack GenAI (services, auth, modèles, notebooks, VRAM). `--local`, `--remote`, `--quick` | GenAI hosting, #1385 |
| `/analyze-slides` | Analyse qualitative deck PPTX via vision AI. `--render`, `--slides` | tracks slides EPITA/ECE |
| `/qc-iterative-improve` | Workflow amélioration stratégies QC (`[strategy\|issue#]`, `--iterations`, `--backtest`) | #1409 trading |
| `/train-model` | Entraîner un modèle ML (thermal-safe GPU, walk-forward + multi-seed + DM). `--dry-run`, `--seeds`, `--folds`, `--bg` | #1454 Training |
| `/genai-iterate` | Itérer un notebook GenAI contre la stack (auth, sous-domaines, quant, GPU/VRAM) via CLI genai-stack. `--service`, `--quant`, `--validate`, `--bg` | #1385 GenAI |

### Skills de référence (chargés à la demande, pas de slash-command actif)

| Skill | Contenu |
|-------|---------|
| `mcp-jupyter` | Référence outils MCP Jupyter (kernels, exécution cellule, Papermill) |
| `notebook-helpers` | Référence `notebook_helpers.py` / `notebook_tools.py` (manipulation, structure) |
| `notebook-patterns` | Patterns pédagogiques d'enrichissement (modèle GameTheory) |

**`/review-student-prs` = canal canonique du recyclage TP** : il applique déjà la convention exercice→exemple ([.claude/rules/exercise-example-labeling.md](../.claude/rules/exercise-example-labeling.md)) + la review bienveillante + bypass CI/template ([.claude/rules/student-pr-reviews.md](../.claude/rules/student-pr-reviews.md)). Ne pas réécrire ce workflow à la main.

## Voir aussi

- [.claude/rules/proactive-coordination.md](../.claude/rules/proactive-coordination.md) — modèle 1 PR/wakeup + main/side-track + délégation async
- [docs/scripts-reference.md](scripts-reference.md) — scripts du dépôt (maintenance, exécution, catalogue)
- [docs/claude-code-config.md](claude-code-config.md) — agents, skills, rules, model selection
