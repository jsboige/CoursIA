---
paths: MyIA.AI.Notebooks/GenAI/**/*
---

# GenAI Configuration Rules

**Documentation complète** (services, modèles, VRAM, quantizations par service, GPU allocation, ComfyUI Qwen Phase 29) : [docs/genai-services.md](../../docs/genai-services.md).

## Règles HARD

- API keys dans `MyIA.AI.Notebooks/GenAI/.env` (template `.env.example`)
- Variables requises : `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `COMFYUI_BEARER_TOKEN`, `HUGGINGFACE_TOKEN`
- Lancer `/validate-genai` ou `python scripts/genai-stack/genai.py validate --full` AVANT exécution de notebooks GenAI
- Hook `block-secrets.py` bloque les `.env` — demander au user d'éditer manuellement

## ComfyUI Qwen — Architecture critique (Phase 29)

Diffère du SDXL standard. À ne PAS modifier sans test :
- VAE : 16 channels (NOT SDXL standard) — `EmptySD3LatentImage`
- Scheduler : `beta` (mandatory)
- CFG : 1.0 (uses `CFGNorm`, not classic CFG)
- `ModelSamplingAuraFlow` : `shift=3.0`
- Loaders séparés : `VAELoader` + `CLIPLoader(type=sd3)` + `UNETLoader` (NOT `CheckpointLoaderSimple`)
- Text encoding : `TextEncodeQwenImageEdit` (NOT `CLIPTextEncode`), negative : `ConditioningZeroOut`

Pipeline complet et workflow JSON : [docs/genai-services.md](../../docs/genai-services.md).

## Scripts validation

Tous dans `scripts/genai-stack/` (preferer le script wrapper `genai.py`) :
- `genai.py docker status` — état services
- `genai.py validate --full` — validation complète
- `genai.py validate --notebooks` — exec notebooks
