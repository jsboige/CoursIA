---
name: validate-genai
description: Validate the GenAI stack (services, authentication, models, notebooks, GPU). Arguments: [all|services|auth|models|notebooks|vram] [--local] [--remote] [--quick]
---

# Validate GenAI Stack

Validate the complete GenAI infrastructure.

**Target**: `$ARGUMENTS`

## Targets

- `all`: Complete validation (default)
- `services`: Docker services connectivity
- `auth`: ComfyUI authentication tokens
- `models`: Available models inventory
- `notebooks`: GenAI notebook execution
- `vram`: GPU/VRAM availability

## Scripts

```bash
python scripts/genai-stack/validate_stack.py       # Full validation
python scripts/genai-stack/validate_notebooks.py   # Notebook execution
python scripts/genai-stack/check_vram.py           # GPU check
python scripts/genai-stack/list_models.py          # Model inventory
python scripts/genai-stack/list_nodes.py           # ComfyUI nodes
python scripts/genai-stack/docker_manager.py       # Docker management
```

## Service Mapping

| Notebooks | Service | Requirement |
|-----------|---------|-------------|
| 01-1, 01-3 | OpenAI API | OPENAI_API_KEY |
| 01-4, 02-3 | SD Forge | Local or myia.io |
| 01-5, 02-1 | ComfyUI Qwen | COMFYUI_AUTH_TOKEN, ~29GB VRAM |
| 02-4 | Z-Image/vLLM | ~10GB VRAM |

## Configuration (.env)

```bash
# MyIA.AI.Notebooks/GenAI/.env
LOCAL_MODE=false
COMFYUI_API_URL=https://qwen-image-edit.myia.io
COMFYUI_AUTH_TOKEN=your_token
OPENAI_API_KEY=sk-...
ZIMAGE_API_URL=https://z-image.myia.io
```
