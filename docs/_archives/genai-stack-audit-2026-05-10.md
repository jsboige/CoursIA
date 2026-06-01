# GenAI Stack Audit Report - T22.12 (issue #456)

**Machine**: po-2023 (RTX 3080 Ti 16GB GPU0 + RTX 3090 24GB GPU1)
**Date**: 2026-05-10
**Data source**: Local config files (VERIFIED) + training knowledge (SUPPOSE)
**Note**: WebSearch API (400), SearXNG (502) unavailable during session. Recommendations qualified SUPPOSE where not verified against live benchmarks.

---

## 1. Image Generation

### Current Stack (VERIFIED from .env files)

| Service | Model | Port | GPU | VRAM |
|---------|-------|------|-----|------|
| ComfyUI Qwen | qwen_image_edit_2509 (fp8) | 8188 | GPU0 | ~29GB (overflows 16GB, partial offload) |
| vLLM Z-Image | Lumina-Next-SFT-diffusers | 8001 | GPU0 | ~10GB |
| SD Forge Turbo | SD Turbo variant | 17861 | GPU1 | ~6GB |
| SD Forge | SD variant | 7860 | GPU0 | ~6GB |
| SD.Next | SD variant | 7861 | GPU0 | ~6GB |

### Top 3 Alternatives (SUPPOSE)

1. **Flux.1 Dev / Schnell** (Black Forest Labs) — 12B params, ~12GB fp8, SOTA text-to-image
2. **SD3.5 Large / Medium** (Stability AI) — MMDiT 8B/16B, ~12-24GB, SD ecosystem compatible
3. **Hunyuan-DiT** (Tencent) — Bilingual EN+CN, ~16GB fp16, good photorealism

### Recommendation: REPLACE SD Forge/SD.Next with Flux.1 Dev fp8

| Component | Action | Rationale |
|-----------|--------|-----------|
| Qwen Image Edit | **KEEP** | Unique image editing, no competitor |
| Lumina-Next-SFT | **KEEP** | Lightweight text-to-image |
| SD Forge / SD.Next / Forge Turbo | **REPLACE with Flux.1 Dev fp8** | Legacy SD obsolete; Flux SOTA at ~12GB |

**VRAM impact**: +6GB on GPU1 (Flux replaces SD Forge Turbo).

---

## 2. STT (Speech-to-Text)

### Current Stack (VERIFIED)

| Service | Model | Port | GPU | VRAM |
|---------|-------|------|-----|------|
| Whisper API | large-v3-turbo (float16) via **faster-whisper** | 8190 | GPU0 | ~5GB |
| Qwen ASR | Qwen3-ASR-1.7B (bfloat16) | 8195 | GPU1 | ~3GB |
| FunASR | Fun-ASR-Nano-2512 | 8194 | GPU1 | ~2GB |

### Already Using Faster-Whisper

The Whisper API service (`docker-configurations/services/whisper-api/app.py`) already uses `faster_whisper.WhisperModel` with CTranslate2 backend. The `COMPUTE_TYPE=float16` is configurable — switching to `int8` would reduce VRAM from ~5GB to ~3GB.

### Recommendation: Switch Whisper COMPUTE_TYPE to int8

| Component | Action | Rationale |
|-----------|--------|-----------|
| Whisper API | **CHANGE compute_type to int8** | Already using faster-whisper; int8 saves ~2GB VRAM with minimal quality loss |
| Qwen3-ASR-1.7B | **KEEP** | 30-language support |
| FunASR Nano | **KEEP** | Niche Chinese STT |

**VRAM savings**: -2GB on GPU0.

---

## 3. TTS (Text-to-Speech)

### Current Stack (VERIFIED)

| Service | Model | Port | GPU | VRAM |
|---------|-------|------|-----|------|
| Kokoro TTS | kokoro (default: af_sky) | 8191 | GPU1 | ~2GB |
| tts-gateway | multi-backend proxy | 8196 | GPU1 | ~0.5GB |

### Recommendation: KEEP Kokoro, optionally ADD F5-TTS

| Component | Action | Rationale |
|-----------|--------|-----------|
| Kokoro TTS | **KEEP** | Lightweight, fast, good quality |
| tts-gateway | **KEEP** | Multi-backend architecture is excellent |
| F5-TTS | **ADD** (optional, LOW priority) | Voice cloning for advanced demos; ~6GB |

---

## 4. Music Generation

### Current Stack (VERIFIED)

| Service | Model | Port | GPU | VRAM |
|---------|-------|------|-----|------|
| MusicGen | facebook/musicgen-medium | 8192 | GPU1 | ~4GB (on-demand) |
| Demucs | htdemucs_ft | 8193 | GPU0 | ~4GB (on-demand) |

### Recommendation: KEEP current (LOW priority)

MusicGen-medium is adequate. Optional upgrade to MusicGen-large (~8GB) if GPU1 headroom available after image upgrades.

---

## 5. Video Generation

### Current Stack (VERIFIED)

| Service | Model | Port | GPU | VRAM |
|---------|-------|------|-----|------|
| ComfyUI Video | AnimateDiff + HunyuanVideo + Wan + SVD + LTX | 8189 | GPU1 | on-demand |

### Recommendation: KEEP, upgrade Wan 2.1 to 2.2

ComfyUI Video meta-service with on-demand loading is the right architecture. Ensure latest model versions.

---

## Summary Table

| Category | Current | Recommendation | Priority | VRAM Impact |
|----------|---------|---------------|----------|-------------|
| **Image** | Qwen + Lumina + SD Forge/SD.Next | REPLACE SD stack with Flux.1 Dev fp8 | HIGH | +6GB GPU1 |
| **STT** | Whisper (faster-whisper float16) + Qwen ASR + FunASR | Switch to int8 compute_type | MEDIUM | -2GB GPU0 |
| **TTS** | Kokoro + tts-gateway | KEEP | — | Neutral |
| **Music** | MusicGen-medium + Demucs | KEEP | LOW | Neutral |
| **Video** | ComfyUI Video (multi-model) | KEEP, update Wan 2.1→2.2 | MEDIUM | Neutral |

## GPU Budget After Recommended Changes

**GPU0 (RTX 3080 Ti, 16GB)**:
- Qwen Image Edit: ~12GB (fp8, partial offload)
- Whisper int8: ~3GB (down from ~5GB)
- Demucs: ~0GB (on-demand)
- **Total steady-state**: ~15GB / 16GB

**GPU1 (RTX 3090, 24GB)**:
- Flux.1 Dev fp8: ~12GB (NEW)
- Kokoro TTS: ~2GB
- tts-gateway: ~0.5GB
- Qwen ASR: ~3GB
- MusicGen: ~4GB (on-demand)
- ComfyUI Video: ~0GB (on-demand)
- **Total steady-state**: ~17.5GB / 24GB (73%)

## Caveats

1. All VRAM estimates for alternatives are SUPPOSE (training knowledge), not live benchmarks
2. Flux fp8 availability must be confirmed with current ComfyUI version
3. Whisper int8 quality loss is minimal but should be validated with NanoClaw E2E test
4. GPU0 at 15/16GB is tight — monitor for OOM during concurrent Qwen + Whisper usage

## Files Referenced

- `docker-configurations/services/whisper-api/app.py` — Whisper API (already uses faster-whisper)
- `docker-configurations/services/whisper-api/.env` — Whisper config (COMPUTE_TYPE=float16)
- `docker-configurations/services/comfyui-qwen/.env` — Qwen Image Edit config
- `docker-configurations/services/tts-api/.env` — Kokoro TTS config
- `docker-configurations/services/musicgen-api/.env` — MusicGen config
- `docker-configurations/services/demucs-api/.env` — Demucs config
- `docker-configurations/services/comfyui-video/.env` — ComfyUI Video config
- `docs/genai-services.md` — Current architecture documentation
