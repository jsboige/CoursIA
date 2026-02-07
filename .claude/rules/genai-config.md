---
paths: MyIA.AI.Notebooks/GenAI/**/*
---

# GenAI Configuration Rules

## Environment

- API keys in `MyIA.AI.Notebooks/GenAI/.env` (template: `.env.example`)
- Required variables: `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `COMFYUI_BEARER_TOKEN`, `HUGGINGFACE_TOKEN`
- Use `/validate-genai` before executing GenAI notebooks

## Services

| Service | Model | VRAM | URL |
|---------|-------|------|-----|
| Qwen Image Edit | qwen_image_edit_2509 | ~29GB | qwen-image-edit.myia.io |
| Z-Image/Lumina | Lumina-Next-SFT | ~10GB | z-image.myia.io |

## Validation Scripts

All in `scripts/genai-stack/`:
- `validate_stack.py` - Full stack validation
- `validate_notebooks.py` - Notebook execution
- `check_vram.py` - GPU check
- `list_models.py` - Model inventory
- `docker_manager.py` - Docker management

## ComfyUI Qwen Architecture

- VAE: 16 channels (NOT SDXL standard)
- Scheduler: `beta` (mandatory)
- CFG: 1.0 (uses CFGNorm, not classic CFG)
- ModelSamplingAuraFlow: shift=3.0

## Docker Services

```bash
cd docker-configurations/services/comfyui-qwen
cp .env.example .env
docker-compose up -d
```
Access: http://localhost:8188 (requires Bearer token authentication)
