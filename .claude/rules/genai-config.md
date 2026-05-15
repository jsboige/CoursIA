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

## Quantization Settings per Service

Optimal quantization for each GenAI service, balancing VRAM savings vs quality.

| Service | Model | Quantization | VRAM | Config |
|---------|-------|-------------|------|--------|
| **comfyui-qwen** | Qwen-Image-Edit-2509 | fp8 (checkpoint) | ~15GB | FP8 safetensors checkpoint, ~50% savings vs bf16 (~29GB) |
| **vllm-zimage** | Z-Image-Turbo | bfloat16 (default), fp8 option | ~10GB bf16 / ~5GB fp8 | `VLLM_QUANTIZATION` env var, `--gpu-memory-utilization 0.35`, `--dtype` flag |
| **whisper-api** | faster-whisper large-v3-turbo | int8_float16 | ~3GB | `WHISPER_COMPUTE_TYPE=int8_float16`, mixed int8+fp16 |
| **qwen-asr-api** | Qwen2-Audio | bfloat16 | ~6GB | `QWEN_ASR_DTYPE=bfloat16` |
| **funasr-api** | FunASR Paraformer | fp16 (default) | ~2GB | No explicit quant config |
| **tts-kokoro** | Kokoro-82M | fp32 (default) | ~1GB | Small model, no quantization needed |
| **tts-qwen** | Qwen-TTS | bfloat16 | ~4GB | vLLM serve, `GPU_MEMORY_UTILIZATION=0.3` |
| **tts-tada** | Tada-TTS | fp32 (default) | ~1GB | Small model, no quantization needed |
| **musicgen-api** | MusicGen-small | fp16 (default) | ~3GB | No explicit quant config |
| **demucs-api** | HTDemucs | fp32 (default) | ~2GB | No quantization needed (inference-only) |
| **forge-turbo** | SDXL-Lightning | xformers fp16 | ~6GB | `--xformers` for memory-efficient attention |
| **sd-forge-main** | SDXL 1.0 | xformers fp16 | ~8GB | `--xformers`, same as forge-turbo |
| **comfyui-video** | AnimateDiff/HunyuanVideo | fp16 (default) | varies | No explicit quant, GPU-intensive |
| **whisper-webui** | Whisper large-v3 | fp16 (default) | ~3GB | No explicit quant config |

### Recommendations

- **comfyui-qwen**: Already using FP8 checkpoint (optimal). No further compression needed.
- **vllm-zimage**: Can switch to FP8 via `VLLM_QUANTIZATION=fp8` in .env for ~5GB VRAM (critical for GPU coexistence). Current default is bfloat16 (~10GB).
- **whisper-api**: int8_float16 is optimal for faster-whisper. No change needed.
- **forge-turbo / sd-forge-main**: xformers is already the best memory optimization for SD WebUI Forge.
- **tts-qwen**: `GPU_MEMORY_UTILIZATION=0.3` keeps it lightweight on shared GPU.

### GPU Allocation (po-2023)

| GPU | Device | Services | Total VRAM |
|-----|--------|----------|------------|
| GPU0 | RTX 3080Ti 16GB | comfyui-qwen (~15GB FP8), whisper-api (~3GB), demucs-api (~2GB) | ~20GB (overcommit) |
| GPU1 | RTX 3090 24GB | vllm-zimage (~5-10GB), forge-turbo (~6GB), tts-qwen (~4GB), musicgen (~3GB), funasr (~2GB), qwen-asr (~6GB) | ~31GB (overcommit) |
