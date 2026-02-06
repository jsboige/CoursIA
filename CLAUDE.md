# CLAUDE.md

Guidance for Claude Code working with the CoursIA repository.

## Project Overview

CoursIA is an educational AI course platform:
- **Jupyter notebooks** for AI learning (C# with .NET Interactive and Python)
- **Docker infrastructure** for GenAI services (ComfyUI + Qwen image editing)
- **GradeBookApp** for student evaluation with collegial grading

Repository: https://github.com/jsboige/CoursIA

## Common Commands

### Environment Setup

```bash
# Python
python -m venv venv && venv\Scripts\activate
pip install -r MyIA.AI.Notebooks/GenAI/requirements.txt

# C# (.NET 9.0)
dotnet restore MyIA.CoursIA.sln

# Docker GenAI
cd docker-configurations/services/comfyui-qwen && cp .env.example .env && docker-compose up -d
```

### Validation & Testing

```bash
python scripts/notebook_tools.py validate [target] --quick    # Structure validation
python scripts/notebook_tools.py execute [target] --cell-by-cell  # Execution
python scripts/genai-stack/validate_stack.py                   # GenAI stack
```

### Claude Code Skills (slash commands)

```
/verify-notebooks [target] [--quick] [--fix]      # Verify and test notebooks
/enrich-notebooks [target] [--execute] [--strict]  # Add pedagogical content
/cleanup-notebooks [target] [--dry-run]             # Clean markdown structure
/build-notebook <action> <path> [--quality=90]      # Create/improve/fix notebooks
/execute-notebook <path> [--batch] [--save]         # Execute via MCP
/validate-genai [target] [--local]                  # Validate GenAI stack
```

### GradeBookApp

```bash
python GradeBookApp/gradebook.py               # Python grading pipeline
python GradeBookApp/run_epf_mis_2026.py         # EPF MIS multi-epreuves
```

## Architecture

```
MyIA.AI.Notebooks/           # Jupyter notebooks by topic
├── GenAI/                   # Image generation, LLMs (Python)
├── ML/                      # ML.NET tutorials (.NET C#)
├── Sudoku/                  # Constraint solving (.NET C#)
├── Search/                  # Optimization (Mixed Python/C#)
├── SymbolicAI/              # RDF, Z3, Tweety, Lean (Mixed)
├── Probas/                  # Infer.NET probabilistic programming (.NET C#)
├── GameTheory/              # OpenSpiel (Python WSL)
├── IIT/                     # PyPhi (Python)
└── Config/                  # API settings (settings.json)

scripts/
├── notebook_helpers.py      # Notebook manipulation (NotebookHelper, CellIterator)
├── notebook_tools.py        # CLI: validate, skeleton, analyze, execute
├── extract_notebook_skeleton.py  # README generation
└── genai-stack/             # GenAI validation scripts

.claude/
├── agents/                  # 10 specialized sub-agents (auto-discovered)
├── skills/                  # 9 skills: 6 user-invocable + 3 reference
└── rules/                   # 5 modular rules (notebook, git, style, genai, wsl)

GradeBookApp/                # Student grading system
docker-configurations/       # ComfyUI + Qwen Docker services
notebook-infrastructure/     # Papermill automation & MCP maintenance
```

## Key Technologies

- **AI/ML**: OpenAI API, Anthropic Claude, Qwen 2.5-VL, Hugging Face, Semantic Kernel
- **Notebooks**: Python 3.10+, .NET 9.0 Interactive, Papermill, MCP Jupyter
- **Docker**: ComfyUI GPU services (RTX 3090, 24GB VRAM)
- **GenAI Models**: DALL-E 3, GPT-5, Qwen Image Edit, Lumina/Z-Image

## Configuration

- **API keys**: `MyIA.AI.Notebooks/GenAI/.env` (template: `.env.example`)
- **C# settings**: `MyIA.AI.Notebooks/Config/settings.json`
- **Docker**: `docker-configurations/services/comfyui-qwen/.env`

## Claude Code Extension Points

### Agents (`.claude/agents/`)

Agents are auto-discovered by Claude Code. Each has YAML frontmatter with model, tools, memory, and skills configuration. Key agents:

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

### Skills (`.claude/skills/`)

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

### Rules (`.claude/rules/`)

| Rule | Scope | Content |
|------|-------|---------|
| notebook-conventions | `*.ipynb` files | Manipulation, structure, execution rules |
| git-workflow | All files | Branch naming, commit messages, safety |
| code-style | All files | PEP 8, .NET, no emojis, naming |
| genai-config | `GenAI/**/*` | Services, env, scripts, architecture |
| wsl-kernels | `GameTheory/**`, `Lean/**` | WSL kernel issues and workarounds |

### Model Selection Strategy

When delegating to sub-agents, use intelligent model selection:
- **haiku**: Quick tasks (README updates, structure scans, simple validation)
- **sonnet**: Standard tasks (enrichment, execution, cleanup, validation)
- **inherit/opus**: Complex tasks (design, orchestration, debugging)

### Proactive Behaviors

- After completing notebook work, **update agent memory** with lessons learned
- After enrichment, **verify cell placement** with git diff
- Before executing GenAI notebooks, **validate the stack** with `/validate-genai`
- When encountering repeated errors, **record the pattern** in memory for future reference
- When working with notebooks, **use the helper scripts** (not ad-hoc Python)

## Language

Primary documentation language: French. Code comments: French or English.
