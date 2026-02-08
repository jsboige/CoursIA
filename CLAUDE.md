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
```

### Docker/ComfyUI Services

```bash
python scripts/genai-stack/genai.py docker status    # Statut des services
python scripts/genai-stack/genai.py docker start all # Demarrer tous les services
python scripts/genai-stack/genai.py docker stop all  # Arreter tous les services
```

### Validation & Testing

```bash
python scripts/genai-stack/genai.py validate --full       # Validation complete ComfyUI
python scripts/genai-stack/genai.py validate --nunchaku   # Test Nunchaku INT4
python scripts/genai-stack/genai.py validate --notebooks  # Validation syntaxe notebooks
python scripts/genai-stack/genai.py notebooks             # Validation Papermill notebooks
python scripts/genai-stack/genai.py gpu                   # Verification VRAM
python scripts/notebook_tools.py validate [target]        # Multi-family notebook verification
```
GitHub Actions validates notebooks on PR (`.github/workflows/notebook-validation.yml`)

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

---

## GenAI Services - ComfyUI Image Generation

### Services disponibles

| Service | Modele | VRAM | Description |
|---------|--------|------|-------------|
| **Qwen Image Edit** | qwen_image_edit_2509 | ~29GB | Edition d'images avec prompts multimodaux |
| **Z-Image/Lumina** | Lumina-Next-SFT | ~10GB | Generation text-to-image haute qualite |

### Architecture Qwen (Phase 29)

Workflow ComfyUI pour Qwen Image Edit 2509 :

```
VAELoader (qwen_image_vae.safetensors, 16 channels)
    |
CLIPLoader (qwen_2.5_vl_7b_fp8_scaled.safetensors, type: sd3)
    |
UNETLoader (qwen_image_edit_2509_fp8_e4m3fn.safetensors)
    |
ModelSamplingAuraFlow (shift=3.0)
    |
CFGNorm (strength=1.0)
    |
TextEncodeQwenImageEdit (clip, prompt, vae)
    |
ConditioningZeroOut (negative)
    |
EmptySD3LatentImage (16 channels)
    |
KSampler (scheduler=beta, cfg=1.0, sampler=euler)
    |
VAEDecode
```

**Points critiques** :
- VAE 16 canaux (pas SDXL standard)
- `scheduler=beta` obligatoire
- `cfg=1.0` (pas de CFG classique, utilise CFGNorm)
- `ModelSamplingAuraFlow` avec shift=3.0

### Architecture Z-Image/Lumina

Workflow ComfyUI simplifie avec LuminaDiffusersNode :

```
LuminaDiffusersNode (Alpha-VLLM/Lumina-Next-SFT-diffusers)
    |
VAELoader (sdxl_vae.safetensors)
    |
VAEDecode
    |
SaveImage
```

**Parametres LuminaDiffusersNode** :
- `model_path`: "Alpha-VLLM/Lumina-Next-SFT-diffusers"
- `num_inference_steps`: 20-40
- `guidance_scale`: 3.0-5.0
- `scaling_watershed`: 0.3
- `proportional_attn`: true
- `max_sequence_length`: 256

**Note technique (Janvier 2025)** : Le node utilise `LuminaPipeline` (diffusers 0.34+), ancien nom `LuminaText2ImgPipeline` obsolete.

### Approches abandonnees

| Approche | Raison abandon |
|----------|----------------|
| Z-Image GGUF | Incompatibilite dimensionnelle (2560 vs 2304) entre RecurrentGemma et Gemma-2 |
| Qwen GGUF | Non teste, prefer les poids fp8 pour qualite |

### Scripts de gestion GenAI (scripts/genai-stack/)

**IMPORTANT pour agents** : Utiliser le CLI unifie `genai.py` au lieu de demarrer des kernels MCP directement.

```bash
# CLI unifie - aide
python scripts/genai-stack/genai.py --help

# Gestion services Docker
python scripts/genai-stack/genai.py docker status          # Statut services
python scripts/genai-stack/genai.py docker start all       # Demarrer tous les services
python scripts/genai-stack/genai.py docker test --remote   # Tester endpoints (local + remote)

# Validation stack ComfyUI
python scripts/genai-stack/genai.py validate --full        # Validation complete
python scripts/genai-stack/genai.py validate --nunchaku    # Test Nunchaku INT4 Lightning

# Validation notebooks
python scripts/genai-stack/genai.py validate --notebooks   # Syntaxe notebooks GenAI
python scripts/genai-stack/genai.py notebooks              # Execution Papermill

# GPU et modeles
python scripts/genai-stack/genai.py gpu                    # Verification VRAM
python scripts/genai-stack/genai.py models list-nodes      # Custom nodes ComfyUI
python scripts/genai-stack/genai.py models list-checkpoints # Checkpoints disponibles

# Authentification
python scripts/genai-stack/genai.py auth audit             # Audit securite tokens
python scripts/genai-stack/genai.py auth sync              # Synchroniser tokens
```

### Mapping notebooks GenAI → services

| Notebooks | Service | Prerequis |
|-----------|---------|-----------|
| 01-1, 01-3 | OpenAI API (cloud) | OPENAI_API_KEY |
| 01-4, 02-3 | SD Forge | Service local ou myia.io |
| 01-5, 02-1 | ComfyUI Qwen | COMFYUI_AUTH_TOKEN, ~29GB VRAM |
| 02-4 | Z-Image/vLLM | ~10GB VRAM |
| 03-* | Multi-modeles | Tous les services |
| 04-* | Applications | Variable |

### Configuration .env GenAI

Fichier : `MyIA.AI.Notebooks/GenAI/.env`

```bash
# Mode local (Docker) vs remote (myia.io)
LOCAL_MODE=false

# ComfyUI
COMFYUI_API_URL=https://qwen-image-edit.myia.io
COMFYUI_AUTH_TOKEN=<bearer_token_bcrypt>

# OpenAI via OpenRouter
OPENAI_API_KEY=sk-or-v1-...
OPENAI_BASE_URL=https://openrouter.ai/api/v1

# Mode batch pour execution automatisee
BATCH_MODE=false
```

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
