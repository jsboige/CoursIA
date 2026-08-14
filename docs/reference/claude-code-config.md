# Claude Code Extension Points

## Agents (`.claude/agents/`)

Agents are auto-discovered by Claude Code. Each has YAML frontmatter with model, tools, memory, and skills configuration. **The roster below lists 9 representative agents** — the **full roster (21 agents)** with descriptions, mapping Epic → specialist, et mapping side-track est dans [subagents-reference.md](subagents-reference.md) (la source de vérité).

| Agent | Model | Purpose |
|-------|-------|---------|
| notebook-iterative-builder | inherit | Orchestrate build/improve/fix cycles |
| notebook-executor | sonnet | Execute notebooks via MCP |
| notebook-validator | sonnet | Validate all quality aspects |
| notebook-enricher | sonnet | Add pedagogical content |
| notebook-cleaner | sonnet | Fix markdown structure |
| notebook-designer | inherit | Create new notebooks |
| notebook-cell-iterator | sonnet | Fix specific cells iteratively |
| readme-updater | haiku | Update README files |
| readme-hierarchy-auditor | haiku | Audit README hierarchy |

## Skills (`.claude/skills/`)

| Skill | Type | Description |
|-------|------|-------------|
| notebook-helpers | Reference (auto) | Script reference for notebook manipulation |
| mcp-jupyter | Reference (auto) | MCP Jupyter tools and patterns |
| notebook-patterns | Reference (auto) | Enrichment patterns (GameTheory model) |
| verify-notebooks | User (`/command`) | Verify and test notebooks |
| enrich-notebooks | User (`/command`) | Enrich with pedagogical content |
| cleanup-notebooks | User (`/command`) | Clean markdown structure |
| build-notebook | User (`/command`) | Create/improve/fix notebooks |
| execute-notebook | User (`/command`) | Execute via MCP |
| validate-genai | User (`/command`) | Validate GenAI stack |

### Slash commands utiles

```
/verify-notebooks [target] [--quick] [--fix]      # Verify and test notebooks
/enrich-notebooks [target] [--execute] [--strict]  # Add pedagogical content
/cleanup-notebooks [target] [--dry-run]             # Clean markdown structure
/build-notebook <action> <path> [--quality=90]      # Create/improve/fix notebooks
/execute-notebook <path> [--batch] [--save]         # Execute via MCP
/validate-genai [target] [--local]                  # Validate GenAI stack
```

## Rules (`.claude/rules/`)

**Toutes auto-chargées à chaque session** — leur contenu est déjà en contexte pour un agent en cours de travail. Cet inventaire sert à qui lit le dépôt sans session active, ou cherche quelle règle porte quel sujet.

| Règle | Ce qu'elle porte |
|---|---|
| `git-workflow` | branches, messages de commit, périmètre force-push, scan de branche orpheline |
| `pr-review-discipline` | critères CHANGES_REQUESTED §A-H (composites, Lean, ML multi-seed, notebooks, docs, audit, QC, SOTA) |
| `anti-regression` | patterns red-flag, protocole avant suppression de preuve/implémentation |
| `notebook-conventions` | structure, exécution kernel, C.1-C.5 |
| `exercise-example-labeling` | classification par contenu, fin du flip-flop exercice/exemple |
| `code-style` | PEP 8, .NET 9, pas d'emojis, i18n Lean FR/EN siblings |
| `genai-config` | services, env, scripts, architecture GenAI |
| `wsl-kernels` | kernels WSL (`GameTheory/**`, `Lean/**`) |
| `student-pr-reviews` | anti-fuite soutenance, review bienveillante |
| `lean-merge-discipline` | gates de merge propres au Lean |
| `secrets-hygiene` · `secrets-roosync-policy` | content-based, Stop & Repair, canal RooSync privé + quorum |
| `audit-reassessment` · `audit-cross-source-distillation` | protocole 4 étapes, sortie = dashboard/issue jamais un fichier |
| `verify-before-claiming` | G.1, firsthand avant tout claim |
| `coordinator-discipline` | R1-R5 ai-01 (merge actif, no languishing, lanes indépendantes, jamais sanctionner l'idle, steer qui atteint) |
| `proactive-coordination` | plancher 1 PR/wakeup, pool global, picker, never-idle, L721/L740/L898 |
| `user-blocker-signaling` | anti-dilution des bloqueurs user |
| `harness-hygiene` | 3 tiers harnais / docs / dashboard |
| `catalog-pr-hygiene` | le catalogue appartient à l'automatisation |
| `model-delegation` | modèle explicite obligatoire, routage vision |
| `three-exercises-per-notebook` | richesse pédagogique |
| `sota-not-workaround` | 5 verdicts, checklist 6 axes INTRINSIC, Prong B |
| `readme-french-first` | français d'abord, anglais préservé en `.en.md` |
| `variation-protocol` | tag `Grain:`, gates G-VAR-1/2/3, merge-gate |
| `lane-claim-protocol` | claim = commentaire d'issue, `paths:`, anti-collision cross-lane |
| `cell-interpretation-ordering` | ancrage sémantique des cellules d'interprétation |

## Model Selection Strategy

**Modèle explicite obligatoire** sur tout `Agent()` — un sous-agent sans `model` hérite du tier parent (opus) et annule l'économie de la délégation. Règle complète : [`.claude/rules/model-delegation.md`](../../.claude/rules/model-delegation.md).

- **`haiku`** : tâches simples (comptage, extraction format-imposé, grep/scan, vérification mécanique)
- **`sonnet`** : tâches intermédiaires (audit, recensement, diagnostic, rédaction, enrichissement, review structurelle)
- **`opus`** : **uniquement** sur justification écrite d'une ligne dans le prompt (décision architecturale cross-fichier, synthèse multi-sources contradictoires, régression profonde)

## Proactive Behaviors

- After completing notebook work, **update agent memory** with lessons learned
- After enrichment, **verify cell placement** with git diff
- Before executing GenAI notebooks, **validate the stack** with `/validate-genai`
- When encountering repeated errors, **record the pattern** in memory for future reference
- When working with notebooks, **use the helper scripts** (not ad-hoc Python)
