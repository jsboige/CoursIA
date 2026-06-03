# Reverse Proxy Circuit — Docker Services → Public URLs

**Host**: po-2023 (Windows Server, IIS Reverse Proxy)
**Last updated**: 2026-05-14
**SHA**: `04d2d6b3`

## Architecture Overview

```
Internet (HTTPS, *.myia.io)
    │
    ▼
IIS Reverse Proxy (po-2023, SSL termination)
    │
    ├── Docker containers (bind 127.0.0.1:<port>)
    │
    ▼
Service response
```

- All Docker services bind to `127.0.0.1:<port>` (localhost only, no direct external access)
- IIS reverse proxy terminates SSL and forwards to the appropriate localhost port
- Reverse proxy configuration is managed at the IIS/server level (NOT in this repository)
- API keys are passed via environment variables in each service's `docker-compose.yml`

## Complete Service Map

### Image Services (5)

| Service | Container | Bind Port | Public URL | .env Variable | GPU | Healthcheck |
|---------|-----------|-----------|------------|---------------|-----|-------------|
| Qwen Image Edit | comfyui-qwen | 8188 | `qwen-image-edit.myia.io` | `COMFYUI_API_URL` | GPU0 3080Ti | `curl localhost:8188` (200/401) |
| Z-Image / Lumina | vllm-zimage | 8001 | `z-image.myia.io` | `ZIMAGE_API_URL` | GPU1 3090 | `curl localhost:8000/health` |
| SD Forge (main) | sd-forge | 7860 | `stable-diffusion-webui-forge.myia.io` | `SD_FORGE_API_URL` | GPU1 3090 | (default) |
| SD Forge Turbo | forge-turbo | 17861 | `turbo.stable-diffusion-webui-forge.myia.io` | `SD_FORGE_TURBO_URL` / `FORGE_API_URL` | GPU1 3090 | (default) |
| SD.Next | sdnext | 7861 | `sdnext.myia.io` | `SDNEXT_API_URL` | GPU1 3090 | (default) |

### Audio Services (5)

| Service | Container | Bind Port | Public URL | .env Variable | GPU | Healthcheck |
|---------|-----------|-----------|------------|---------------|-----|-------------|
| Whisper STT | whisper-api | 8190 | `whisper-api.myia.io` | `WHISPER_API_URL` | GPU0 3080Ti | `curl localhost:8190/health` |
| Kokoro TTS (standalone) | tts-api | 8191 | `tts-api.myia.io` | `TTS_API_URL` | GPU1 3090 | `curl localhost:8191/health` |
| MusicGen | musicgen-api | 8192 | `musicgen-api.myia.io` | `MUSICGEN_API_URL` | GPU1 3090 | `curl localhost:8192/health` |
| Demucs | demucs-api | 8193 | `demucs-api.myia.io` | `DEMUCS_API_URL` | GPU0 3080Ti | `curl localhost:8193/health` |
| FunASR | funasr-api | 8194 | `stt.myia.io/funasr` | — | GPU1 3090 | `curl localhost:8194/health` |

### Audio Services — TTS Gateway (3-in-1)

The TTS Gateway (`tts-multi`) provides a single entry point routing to 3 backend models:

| Component | Container | Bind Port | Public URL Path | GPU |
|-----------|-----------|-----------|-----------------|-----|
| TTS Gateway | tts-gateway | 8196 | `tts-api.myia.io` | CPU (no GPU) |
| ├─ Kokoro | tts-kokoro | (internal) | `/v1/audio/speech` | GPU1 3090 |
| ├─ TADA 3B | tts-tada | (internal) | `/tada/v1/audio/speech` | GPU1 3090 |
| └─ Qwen3 TTS | tts-qwen | (internal) | `/qwen/v1/audio/speech` | GPU1 3090 |

.env variables: `KOKORO_TTS_URL`, `TADA_TTS_URL`, `QWEN_TTS_URL` (all via `tts-api.myia.io/...`)

### ASR Service — Qwen

| Service | Container | Bind Port | Public URL | GPU | Healthcheck |
|---------|-----------|-----------|------------|-----|-------------|
| Qwen ASR | qwen-asr-api | 8195 | `stt.myia.io/qwen` | GPU1 3090 | `curl localhost:8195/health` |

### Video Service (1)

| Service | Container | Bind Port | Public URL | .env Variable | GPU | Healthcheck |
|---------|-----------|-----------|------------|---------------|-----|-------------|
| ComfyUI Video | comfyui-video | 8189 | `comfyui-video.myia.io` | `COMFYUI_VIDEO_URL` | GPU0 3090 | `curl localhost:8188` (200/401) |

Note: ComfyUI Video runs on GPU0 (RTX 3090) and is **mutually exclusive** with comfyui-qwen (same GPU). Internal port is 8188, mapped to host port 8189.

## GPU Allocation

| GPU | Hardware | Services | Approx VRAM |
|-----|----------|----------|-------------|
| GPU 0 | RTX 3080 Ti 16GB | comfyui-qwen (29GB model), comfyui-video, whisper-api, demucs-api | ~98% (comfyui-qwen active) |
| GPU 1 | RTX 3090 24GB | vllm-zimage, forge-turbo, sdnext, sd-forge, tts-kokoro, tts-tada, tts-qwen, musicgen-api, funasr-api, qwen-asr-api | ~36% (idle-unload active) |

GPU contention: Z-Image (vLLM) and Forge Turbo share GPU1 with audio services. Idle monitors auto-unload models after timeout.

## Port Allocation Table

| Port | Service | Protocol | Auth |
|------|---------|----------|------|
| 7860 | sd-forge | HTTP | API key |
| 7861 | sdnext | HTTP | User/password |
| 8001 | vllm-zimage | HTTP (OpenAI-compat) | API key |
| 8188 | comfyui-qwen | HTTP | Bearer token |
| 8189 | comfyui-video | HTTP | Bearer token |
| 8190 | whisper-api | HTTP (OpenAI-compat) | API key |
| 8191 | tts-api (Kokoro standalone) | HTTP (OpenAI-compat) | API key |
| 8192 | musicgen-api | HTTP | API key |
| 8193 | demucs-api | HTTP | API key |
| 8194 | funasr-api | HTTP (OpenAI-compat) | API key |
| 8195 | qwen-asr-api | HTTP (OpenAI-compat) | API key |
| 8196 | tts-gateway | HTTP (OpenAI-compat) | API key |
| 17861 | forge-turbo | HTTP | User/password |

## Hybrid Configurations

Two services have alternate `docker-compose-hybrid.yml` files for po-2023 deployment using pre-built GHCR images:

| Service | Standard | Hybrid (po-2023) |
|---------|----------|------------------|
| Whisper API | Local build, GPU0 | `ghcr.io/myia-org/whisper-api:latest`, GPU1 |
| Kokoro TTS | Local build, GPU1 | `ghcr.io/myia-org/kokoro-tts:latest`, GPU1 |

Hybrid configs bind to `0.0.0.0` instead of `127.0.0.1` (direct port exposure).

## API Key Locations

| Scope | File | Keys |
|-------|------|------|
| GenAI notebooks | `MyIA.AI.Notebooks/GenAI/.env` | COMFYUI_*, ZIMAGE_*, SD_FORGE_*, WHISPER_*, TTS_*, MUSICGEN_*, DEMUCS_*, OPENAI_*, ANTHROPIC_* |
| Whisper API service | `docker-configurations/services/whisper-api/.env` | WHISPER_API_KEY |
| TTS API service | `docker-configurations/services/tts-api/.env` | TTS_API_KEY |
| TTS Gateway service | `docker-configurations/services/tts-multi/.env` | TTS_GATEWAY_API_KEY |
| MusicGen service | `docker-configurations/services/musicgen-api/.env` | MUSICGEN_API_KEY |
| Demucs service | `docker-configurations/services/demucs-api/.env` | DEMUCS_API_KEY |
| FunASR service | `docker-configurations/services/funasr-api/.env` | FUNASR_API_KEY |
| Qwen ASR service | `docker-configurations/services/qwen-asr-api/.env` | QWEN_ASR_API_KEY |
| ComfyUI Qwen | `docker-configurations/services/comfyui-qwen/.env` | COMFYUI_BEARER_TOKEN |
| ComfyUI Video | `docker-configurations/services/comfyui-video/.env` | COMFYUI_VIDEO_TOKEN |
| Forge Turbo | `docker-configurations/services/forge-turbo/.env` | FORGE_USER, FORGE_PASSWORD |
| vLLM Z-Image | `docker-configurations/services/vllm-zimage/.env` | VLLM_API_KEY |

## Reverse Proxy Configuration

The IIS reverse proxy on po-2023 maps public HTTPS domains to localhost ports. This configuration is **NOT stored in this repository** — it is managed at the server level.

Typical IIS URL Rewrite rules:
- Match pattern: `*(.myia.io)` → rewrite to `http://127.0.0.1:<port>`
- SSL certificates: Let's Encrypt or IIS-managed
- Additional headers: `X-Forwarded-For`, `X-Forwarded-Proto`

To modify reverse proxy rules: connect to po-2023 via RDP and edit IIS Manager → URL Rewrite rules.

## Diagnostics

### Quick healthcheck all services (from po-2023)

```bash
# Check all localhost ports
for port in 7860 7861 8001 8188 8189 8190 8191 8192 8193 8194 8195 8196 17861; do
  status=$(curl -s -o /dev/null -w "%{http_code}" http://localhost:$port/health 2>/dev/null || echo "CONN_FAIL")
  echo "Port $port: $status"
done
```

### Check from external (Internet)

```bash
# Verify public URLs resolve and proxy works
curl -s -o /dev/null -w "%{http_code}" https://whisper-api.myia.io/health
curl -s -o /dev/null -w "%{http_code}" https://qwen-image-edit.myia.io/
curl -s -o /dev/null -w "%{http_code}" https://z-image.myia.io/health
```
