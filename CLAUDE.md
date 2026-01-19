# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

CoursIA is an educational AI course platform combining:
- **Jupyter notebooks** for AI learning (C# with .NET Interactive and Python)
- **Docker infrastructure** for GenAI services (ComfyUI + Qwen image editing)
- **Production-ready ecosystem** with authentication, orchestration, and validation

Repository: https://github.com/jsboige/CoursIA

## Build & Setup Commands

### Python Environment
```bash
python -m venv venv
venv\Scripts\activate  # Windows
source venv/bin/activate  # Linux/macOS
pip install -r MyIA.AI.Notebooks/GenAI/requirements.txt
python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"
```

### C# Notebooks (.NET Interactive)
```bash
dotnet restore MyIA.CoursIA.sln
```
Configuration: Copy `MyIA.AI.Notebooks/Config/settings.json.openai-example` to `settings.json`

### Docker/ComfyUI Services
```bash
cd docker-configurations/comfyui-qwen
cp .env.example .env
docker-compose up -d
```
Access: http://localhost:8188 (requires Bearer token authentication)

## Validation & Testing

### Notebook Validation
GitHub Actions validates notebooks on PR (`.github/workflows/notebook-validation.yml`)
```bash
python scripts/genai-stack/validate_notebooks.py
```

### GenAI Stack Validation
```bash
python scripts/genai-stack/validate_stack.py
python scripts/genai-stack/check_vram.py
```

## Architecture

```
MyIA.AI.Notebooks/           # Educational content (18 notebooks)
├── GenAI/                   # GenAI ecosystem (image generation, LLMs)
├── ML/                      # Machine Learning with ML.NET (C#)
├── SymbolicAI/              # Z3 solver, OR-Tools, RDF
├── Sudoku/                  # 6 solving approaches
├── Search/                  # Genetic algorithms
├── Probas/                  # Probabilistic inference
└── IIT/                     # Integrated Information Theory

docker-configurations/       # Production infrastructure
├── comfyui-qwen/           # Main ComfyUI + Qwen service
├── models/                 # Shared model storage
├── cache/                  # Shared cache layer
└── orchestrator/           # Service orchestration

scripts/
├── genai-stack/            # Validation and management
└── notebook-fixes/         # Notebook repair utilities
```

### GenAI Notebooks Structure (4 levels)
- **00-GenAI-Environment**: Setup and configuration
- **01-Images-Foundation**: DALL-E 3, GPT-5, basic operations
- **02-Images-Advanced**: Qwen, FLUX, Stable Diffusion 3.5, Z-Image
- **03-Images-Orchestration**: Multi-model comparison, workflows
- **04-Images-Applications**: Educational content, production integration

## Code Style Guidelines

- **No emojis** in code, variable names, or generated files
- Follow PEP 8 for Python, standard conventions for C#
- Keep naming professional and descriptive
- Avoid prefixes like "Pure", "Enhanced", "Advanced", "Ultimate" - use descriptive names instead
- Do not commit without explicit user approval

### Branch Naming
```
type/name-short-descriptif
```
Examples: `feature/notebook-transformers`, `fix/ml-example-bug`, `docs/improve-readme`

### Commit Messages
```
Type: description courte de la modification
```
Examples: `Add: notebook sur les Transformers`, `Fix: correction d'erreurs dans l'exemple ML.NET`

## Key Technologies

- **AI/ML**: OpenAI API, Anthropic Claude, Qwen 2.5-VL, Hugging Face, Diffusers
- **ComfyUI**: Custom Qwen nodes (16-channel VAE, vision tokens, multi-image editing)
- **Docker**: Containerized GPU services (RTX 3090, 24GB VRAM recommended)
- **.NET**: ML.NET, .NET Interactive for C# notebooks
- **Jupyter**: Python and C# kernels, papermill for execution

## API Keys Configuration

GenAI notebooks require API keys in `MyIA.AI.Notebooks/GenAI/.env`:
- `OPENAI_API_KEY` - DALL-E 3, GPT models
- `ANTHROPIC_API_KEY` - Claude Vision
- `COMFYUI_BEARER_TOKEN` - Local ComfyUI access
- `HUGGINGFACE_TOKEN` - Hugging Face models

## Hardware Requirements

For ComfyUI/Qwen services:
- GPU: RTX 3090 (24GB VRAM) recommended
- RAM: 32GB+ recommended
- Storage: 100GB+ for models
