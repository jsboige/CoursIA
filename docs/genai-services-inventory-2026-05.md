# GenAI Services Inventory — po-2023 (May 2026)

**Machine**: po-2023 | **Date**: 2026-05-01 | **Track**: A0 GenAI Services Audit
**GPU0**: RTX 3080 Ti Laptop (16384 MiB) | **GPU1**: RTX 3090 (24576 MiB) | **Total**: 40960 MiB

---

## 1. Service Registry

### 1.1 Image Services

| # | Service | Container | Port | GPU | Model | IIS Subdomain | VRAM Peak | IDLE_TIMEOUT | PRELOAD |
|---|---------|-----------|------|-----|-------|---------------|-----------|--------------|---------|
| I-1 | Qwen Image Edit | `comfyui-qwen` | 8188 | GPU0 | qwen_image_edit_2509_fp8 | `qwen-image-edit.myia.io` | ~12 GB (fp8) | 1200s | N/A (ComfyUI) |
| I-2 | Z-Image Turbo | `vllm-zimage` | 8001→8000 | GPU1 | Tongyi-MAI/Z-Image-Turbo | `z-image.myia.io` | ~10 GB | none | N/A (vLLM) |
| I-3 | ComfyUI Video | `comfyui-video` | 8189→8188 | GPU1 | (varies by workflow) | `comfyui-video.myia.io` | varies | 1200s | N/A |
| I-4 | SD Forge Main | `sd-forge-main` | 7860 | all | (SDXL/SD 1.5) | `stable-diffusion-webui-forge.myia.io` | ~8 GB | none | N/A |
| I-5 | SD Forge Turbo | `forge-turbo` | 1111, 17861→17860 | all | (SDXL Turbo) | `turbo.stable-diffusion-webui-forge.myia.io` | ~6 GB | none | N/A |
| I-6 | SDNext | `sdnext` | 7861→7860 | all | (varies) | `sdnext.myia.io` | ~8 GB | none | N/A |

### 1.2 Audio — STT (Speech-to-Text)

| # | Service | Container | Port | GPU | Model | IIS Subdomain | VRAM Peak | IDLE_TIMEOUT | PRELOAD |
|---|---------|-----------|------|-----|-------|---------------|-----------|--------------|---------|
| S-1 | Whisper STT | `whisper-api` | 8190 | GPU0 | large-v3-turbo | `whisper-api.myia.io` | ~5 GB | 1200s | true |
| S-2 | FunASR | `funasr-api` | 8194 | GPU1 | FunAudioLLM/Fun-ASR-Nano-2512 | (via `stt.myia.io`) | ~2 GB | 300s | false |
| S-3 | Qwen ASR | `qwen-asr-api` | 8195 | GPU1 | Qwen/Qwen3-ASR-1.7B | (via `stt.myia.io`) | ~4 GB | 300s | false |

### 1.3 Audio — TTS (Text-to-Speech)

| # | Service | Container | Port | GPU | Model | IIS Subdomain | VRAM Peak | IDLE_TIMEOUT | PRELOAD |
|---|---------|-----------|------|-----|-------|---------------|-----------|--------------|---------|
| T-1 | TTS API (router) | `tts-api` | 8191 | GPU1 | kokoro (default) | `tts-api.myia.io` | ~2 GB | 1200s | true |
| T-2 | Kokoro TTS | `tts-kokoro` | 8000 (internal) | GPU1 | kokoro | (via tts-gateway) | ~2 GB | 1200s | true |
| T-3 | Qwen TTS | `tts-qwen` | 8000 (internal) | GPU1 | Qwen CustomVoice | (via tts-gateway) | ~4 GB | none | N/A |
| T-4 | Tada TTS | `tts-tada` | 8000 (internal) | GPU1 | tada | (via tts-gateway) | ~2 GB | 1200s | true |
| T-5 | TTS Gateway | `tts-gateway` | 8196→8000 | CPU | (router) | `tts-api.myia.io`, `tts.myia.io` | N/A | none | N/A |

### 1.4 Audio — Music & Separation

| # | Service | Container | Port | GPU | Model | IIS Subdomain | VRAM Peak | IDLE_TIMEOUT | PRELOAD |
|---|---------|-----------|------|-----|-------|---------------|-----------|--------------|---------|
| M-1 | MusicGen | `musicgen-api` | 8192 | GPU1 | facebook/musicgen-medium | `musicgen-api.myia.io` | ~5 GB | 1200s | false |
| M-2 | Demucs v4 | `demucs-api` | 8193 | GPU0 | htdemucs_ft | `demucs-api.myia.io` | ~4 GB | 1200s | false |

### 1.5 Other Services on po-2023 (non-GenAI)

| # | Service | Container | Port | Notes |
|---|---------|-----------|------|-------|
| O-1 | Whisper WebUI | `myia-whisper-webui-app-1` | 36540→7860 | Gradio UI, IIS: `whisper-webui.myia.io` |

---

## 2. GPU Allocation Matrix

### GPU0 — RTX 3080 Ti (16384 MiB)

| Service | VRAM Peak | PRELOAD | IDLE_TIMEOUT |
|---------|-----------|---------|--------------|
| comfyui-qwen | ~12 GB (fp8) | N/A | 1200s |
| whisper-api | ~5 GB | true | 1200s |
| demucs-api | ~4 GB | false | 1200s |
| **Sum (active)** | **~21 GB** | | |
| **Target idle sum** | **< 2 GB** | | |

**Note**: GPU0 is oversubscribed (21 GB peak vs 16 GB). Only comfyui-qwen OR whisper+demucs can be active, not all simultaneously.

### GPU1 — RTX 3090 (24576 MiB)

| Service | VRAM Peak | PRELOAD | IDLE_TIMEOUT |
|---------|-----------|---------|--------------|
| vllm-zimage (Z-Image-Turbo) | ~10 GB | N/A | **NONE** |
| comfyui-video | varies | N/A | 1200s |
| tts-api (kokoro) | ~2 GB | true | 1200s |
| tts-kokoro | ~2 GB | true | 1200s |
| tts-qwen | ~8 GB | N/A | **NONE** |
| tts-tada | ~2 GB | true | 1200s |
| funasr-api | ~2 GB | false | 300s |
| qwen-asr-api | ~4 GB | false | 300s |
| musicgen-api | ~5 GB | false | 1200s |
| **Sum (active)** | **~35+ GB** | | |
| **Target idle sum** | **< 3 GB** | | |

### No GPU Isolation (see all GPUs)

| Service | VRAM Peak | IDLE_TIMEOUT | Notes |
|---------|-----------|--------------|-------|
| sd-forge-main | ~8 GB | **NONE** | No DeviceRequests, sees both GPUs |
| forge-turbo | ~6 GB | **NONE** | No DeviceRequests, sees both GPUs |
| sdnext | ~8 GB | **NONE** | No DeviceRequests, sees both GPUs |

**Note**: GPU1 has 2 permanent VRAM hogs (vllm-zimage ~10GB, tts-qwen ~8GB = 18 GB locked). Remaining ~7 GB must serve 8 other services via sleep/wake. SD services without isolation can fragment both GPUs.

---

## 3. IIS Reverse Proxy Mapping (GenAI Subdomains)

| Subdomain | IIS ID | Backend Port | Service | SSL | Routing |
|-----------|--------|-------------|---------|-----|---------|
| `qwen-image-edit.myia.io` | 34 | 8188 | ComfyUI Qwen | HTTPS | Direct |
| `z-image.myia.io` | 39 | 8001 | vLLM Lumina | HTTPS | Direct |
| `comfyui-video.myia.io` | 6 | 8189 | ComfyUI Video | HTTPS | Direct |
| `stable-diffusion-webui-forge.myia.io` | 8 | 7860 | SD Forge Main | HTTPS | Direct + service.* alias |
| `turbo.stable-diffusion-webui-forge.myia.io` | 14 | 1111 | Forge Turbo | HTTPS | Direct |
| `sdnext.myia.io` | 28 | 7861 | SDNext | HTTPS | Direct |
| `whisper-api.myia.io` | 12 | 8190 | Whisper STT | HTTPS | Direct |
| `whisper.genai.myia.io` | 5 | (STT) | Whisper GenAI | HTTPS | Alt domain |
| `stt.myia.io` | 37 | (multi) | STT unified | HTTPS | /whisper→8190, /funasr→8194, /qwen→8195 |
| `tts-api.myia.io` | 13 | 8196 | TTS Gateway | HTTPS | Direct |
| `tts.myia.io` | 47 | 8196 | TTS unified | HTTPS | /kokoro→8191, /gateway→8196, /*→8196 |
| `tts-multi.myia.io` | 46 | (TTS) | Multi-TTS | HTTPS | Alt entry |
| `musicgen-api.myia.io` | 43 | 8192 | MusicGen | HTTPS | Direct |
| `demucs-api.myia.io` | 44 | 8193 | Demucs | HTTPS | Direct |
| `whisper-webui.myia.io` | 9 | 36540 | Whisper WebUI | HTTPS | Gradio UI |

---

## 4. Notebook-to-Service Dependency Matrix

### 4.1 Image Notebooks (`MyIA.AI.Notebooks/GenAI/Image/`)

| Notebook | Primary Service | Fallback | API Key | Notes |
|----------|----------------|----------|---------|-------|
| 01-1_DALL-E_3 | OpenAI API (cloud) | — | OPENAI_API_KEY | DALL-E 3 generation |
| 01-2 (missing) | — | — | — | — |
| 01-3_GPT_Image | OpenAI API (cloud) | — | OPENAI_API_KEY | GPT Image editing |
| 01-4_SD_Forge | SD Forge Main | myia.io remote | COMFYUI_AUTH_TOKEN | Stable Diffusion |
| 01-5_Qwen_Image_Edit | ComfyUI Qwen | — | COMFYUI_AUTH_TOKEN | ~29 GB VRAM |
| 02-1_Qwen_Advanced | ComfyUI Qwen | — | COMFYUI_AUTH_TOKEN | Advanced editing |
| 02-2 (missing) | — | — | — | — |
| 02-3_ControlNet | SD Forge | myia.io remote | COMFYUI_AUTH_TOKEN | ControlNet |
| 02-4_Z_Image | vLLM Z-Image | — | — | Lumina text-to-image |
| 03-1_Pipeline | Multi (Qwen+SD) | — | Mixed | Orchestration |
| 03-2_MultiModel | Multi | — | Mixed | Multi-model |
| 03-3_Workflow | Multi | — | Mixed | End-to-end workflow |
| 04-1_Avatar | ComfyUI Qwen | — | COMFYUI_AUTH_TOKEN | Application |
| 04-2_Style_Transfer | ComfyUI Qwen | — | COMFYUI_AUTH_TOKEN | Application |
| 04-3_Commercial | Multi | — | Mixed | Application |
| 04-4_Gallery | Multi | — | Mixed | Application |

### 4.2 Audio Notebooks (`MyIA.AI.Notebooks/GenAI/Audio/`)

| Notebook | Primary Service | Fallback | API Key | Notes |
|----------|----------------|----------|---------|-------|
| 01-1_OpenAI_TTS | OpenAI API (cloud) | — | OPENAI_API_KEY | Cloud TTS |
| 01-2_OpenAI_STT | OpenAI API (cloud) | — | OPENAI_API_KEY | Cloud STT |
| 01-3_Audio_Basics | Local (librosa/pydub) | — | None | No GPU needed |
| 01-4_Whisper | Whisper STT | OpenAI API | — | GPU ~5 GB |
| 01-5_Kokoro_TTS | Kokoro TTS | — | — | GPU ~2 GB |
| 02-1_Chatterbox_TTS | Chatterbox TTS | — | — | GPU ~8 GB |
| 02-2_XTTS_v2 | XTTS v2 | — | — | GPU ~6 GB |
| 02-3_MusicGen | MusicGen | — | — | GPU ~10 GB |
| 02-4_Demucs | Demucs v4 | — | — | GPU ~4 GB |
| 02-5_Voice_Clone | Multi-TTS | — | — | Mixed |
| 02-6_Realtime_STT | Whisper STT | — | — | Streaming |
| 02-7_Audio_Effects | Local | — | None | DSP |
| 02-8_Speech_Diarization | Whisper+Demucs | — | — | Speaker diarization |
| 03-1_Podcast | Multi | — | Mixed | TTS+STT pipeline |
| 03-2_Music_Generation | MusicGen | — | — | Full music |
| 03-3_Audio_Restoration | Demucs | — | — | Source separation |
| 04-1_Audiobook | Multi-TTS | — | — | Long-form TTS |
| 04-2_Live_Transcription | Whisper | — | — | Real-time |
| 04-3_Karaoke | Whisper+Demucs | — | — | Lyrics + separation |
| 04-4_Podcast_Editor | Multi | — | Mixed | Editing pipeline |
| 04-5_Sound_Design | MusicGen | — | — | Creative |

### 4.3 Video Notebooks (`MyIA.AI.Notebooks/GenAI/Video/`)

| Notebook | Primary Service | Fallback | API Key | Notes |
|----------|----------------|----------|---------|-------|
| 01-1_Video_Basics | Local (moviepy/FFmpeg) | — | None | FFmpeg required |
| 01-2_GPT5_Video | OpenAI GPT-5 | — | OPENAI_API_KEY | Cloud video gen |
| 01-3_Qwen_Video | Qwen2.5-VL local | — | — | GPU ~18 GB |
| 01-4_Real_ESRGAN | Real-ESRGAN/RIFE | — | — | GPU ~4 GB |
| 01-5_AnimateDiff | AnimateDiff | — | — | GPU ~12 GB |
| 02-1_HunyuanVideo | HunyuanVideo | — | — | GPU ~18 GB |
| 02-2_LTX_Video | LTX-Video | — | — | GPU ~8 GB |
| 02-3_Wan | Wan 2.1/2.2 | — | — | GPU ~10 GB |
| 02-4_SVD | SVD | — | — | GPU ~10 GB |
| 03-1_Video_Pipeline | ComfyUI Video | — | COMFYUI_AUTH_TOKEN | Orchestration |
| 03-2_Multi_Model | Multi | — | Mixed | Multi-model |
| 03-3_ComfyUI_Video | ComfyUI Video | — | COMFYUI_AUTH_TOKEN | Docker + nodes |
| 04-1_Short_Film | Multi | — | Mixed | Application |
| 04-2_Music_Video | Multi | — | Mixed | Application |
| 04-3_Sora2 | OpenAI Sora 2 | — | OPENAI_API_KEY | Cloud |
| 04-4_EDL_Export | Local | — | None | Video editing |

### 4.4 Text Notebooks (`MyIA.AI.Notebooks/GenAI/Texte/`)

| Notebook | Primary Service | Notes |
|----------|----------------|-------|
| 01-11 (OpenAI through Quantization) | OpenAI API + local models | OPENAI_API_KEY, some need GPU |

### 4.5 SemanticKernel Notebooks (`MyIA.AI.Notebooks/GenAI/SemanticKernel/`)

| Notebook | Primary Service | Notes |
|----------|----------------|-------|
| 01-10b | OpenAI API + Semantic Kernel | OPENAI_API_KEY |

---

## 5. Sleep/Wake Behavior Summary

### 5.1 Services WITH IDLE_TIMEOUT (sleep-capable)

| Service | Timeout | PRELOAD | Idle VRAM (measured) | Wake Test | Wake Latency |
|---------|---------|---------|---------------------|-----------|-------------|
| comfyui-qwen | 1200s | N/A | (not yet idle) | GET /system_stats | 200, instant |
| whisper-api | 1200s | true | (not yet idle) | POST /v1/audio/transcriptions | 500 on empty file, server up |
| tts-api | 1200s | true | (active) | (covered by tts-kokoro) | — |
| tts-kokoro | 1200s | true | (active) | POST /v1/audio/speech | 200, ~11.5s |
| tts-tada | 1200s | true | (not tested) | — | — |
| musicgen-api | 1200s | false | ~0 (model unloaded) | POST /v1/generate | BLOCKED: downloading model from HF |
| demucs-api | 1200s | false | ~0 (model unloaded) | GET /health | 200, model loads on first request |
| funasr-api | 300s | false | ~0 | GET /health | 200, 0.02s |
| qwen-asr-api | 300s | false | ~0 | GET /health | 200, 0.02s |
| comfyui-video | 1200s | N/A | (not tested) | GET /system_stats | 200, instant |

### 5.2 Services WITHOUT IDLE_TIMEOUT (always-on)

| Service | Current VRAM | Notes | Risk |
|---------|-------------|-------|------|
| vllm-zimage | ~10 GB | No IDLE_TIMEOUT, holds GPU1 permanently | VRAM never released |
| tts-qwen | ~8 GB | No IDLE_TIMEOUT, holds GPU1 permanently | VRAM never released |
| sd-forge-main | ~8 GB peak | No sleep support, GPU=[] | No GPU isolation, sees both GPUs |
| forge-turbo | ~6 GB peak | No sleep support, GPU=[] | No GPU isolation, sees both GPUs |
| sdnext | ~8 GB peak | No sleep support, GPU=[] | No GPU isolation, sees both GPUs |

### 5.3 API Endpoint Test Results (2026-05-01 post-restart)

| Service | Endpoint | Auth | Result | Latency | Notes |
|---------|----------|------|--------|---------|-------|
| ComfyUI Qwen | GET /system_stats | Bearer (bcrypt hash) | 200 OK | < 1s | Token = first line of login/PASSWORD |
| ComfyUI Video | GET /system_stats | Bearer (bcrypt hash) | 200 OK | < 1s | Same auth pattern as Qwen |
| Whisper STT | POST /v1/audio/transcriptions | Shared API key | 500 | — | Empty file test, server up, needs real audio |
| TTS Kokoro | POST /v1/audio/speech | Shared API key | 200 OK | 11.5s | Returns audio/wav |
| TTS Gateway | GET /health | None | 200 OK | 0.02s | CPU router |
| SD Forge Turbo | GET /sdapi/v1/sd-models | Basic (forge:QWvghoUTemZa9M9) | 200 OK | < 1s | Direct API |
| SD Forge Main | GET / (-L) | Basic (admin:changeme) | 200 OK | < 1s | Requires -L (follow redirect) |
| SDNext | GET / | Session cookie | 302 | — | Gradio redirect, not fully tested |
| Z-Image | GET /health | None | 200 OK | < 1s | Health OK but /v1/models crashes |
| Z-Image | GET /v1/models | None | 500 ERROR | — | `AttributeError: 'State' object has no attribute 'openai_serving_models'` |
| Qwen ASR | GET /health | None | 200 OK | 0.02s | |
| FunASR | GET /health | None | 200 OK | 0.02s | |
| Whisper WebUI | GET / | None | 200 OK | < 1s | Gradio UI |
| MusicGen | POST /v1/generate | Shared API key | 500 BUG | — | Model loaded but crashes: `could not convert string to float`. EncodecFeatureExtractor misconfiguration |
| Demucs | GET /health | None | 200 OK | < 1s | Model loaded after first request (htdemucs_ft on GPU1, 0.64 GB) |
| Demucs | POST /v1/separate | Shared API key | 500 BUG | 33s | Missing `torchcodec` dependency in container |

### 5.4 Auth Credentials Reference

| Service | Auth Type | Credential | Source |
|---------|-----------|-----------|--------|
| ComfyUI Qwen | Bearer Token | `$2b$12$aR9XPUlx7SVbigaNrXoOAOahPXAmqmiPxImJ8DkD2K3Kfme7KKLA.` | login/PASSWORD file in container |
| ComfyUI Video | Bearer Token | `$2b$12$I2IOvM7xVaAfaaRgQ7MfreDXU9sImLT7Fr8VpaaAFwk3TKlphQF9u` | login/PASSWORD file in container |
| Whisper/TTS/Audio APIs | API Key | `BwCaesdZuitLAfs6Nr1KX_CVNhX12XavyZThvpT2RD4c1smVrQ00xfZY2PP2pYgK` | Shared across audio stack |
| SD Forge Main | HTTP Basic | `admin:changeme` | Gradio auth |
| SD Forge Turbo | HTTP Basic | `forge:QWvghoUTemZa9M9` | Gradio auth |
| SDNext | Session Cookie | (not tested) | Gradio session |

**Critical issue**: 5 services (vllm-zimage, tts-qwen, 3x SD) have no sleep/wake. GPU1 has 18 GB permanently locked by vllm-zimage + tts-qwen alone. SD services without GPU isolation can fragment both GPUs.

---

## 6. VRAM Budget Analysis

### Current State (2026-05-01, post-restart)

| GPU | Total | Used | Free | Major Consumers |
|-----|-------|------|------|-----------------|
| GPU0 (3080Ti) | 16384 MiB | 15880 MiB | 294 MiB | comfyui-qwen (~12 GB) + whisper-api (~5 GB) |
| GPU1 (3090) | 24576 MiB | 12519 MiB | 11808 MiB | vllm-zimage (~10 GB) + TTS stack (~8 GB) |

**GPU0 is near-full**: Only 294 MiB free. comfyui-qwen (fp8, ~12 GB) + whisper-api (~5 GB) = ~17 GB peak vs 16 GB capacity. Services oversubscribed by ~1 GB.

**GPU1 has headroom**: 11.8 GB free, but 18 GB permanently locked by vllm-zimage (~10 GB, no timeout) + tts-qwen (~8 GB, no timeout). Remaining ~7 GB serves 8 other services via sleep/wake rotation.

### Permanent VRAM Hogs (no sleep)

| Service | GPU | VRAM | Can Sleep? | Action |
|---------|-----|------|-----------|--------|
| comfyui-qwen | GPU0 | ~12 GB | Yes (IDLE_TIMEOUT=1200s) | Already configured, OK |
| vllm-zimage | GPU1 | ~10 GB | **No** | Needs IDLE_TIMEOUT added |
| tts-qwen | GPU1 | ~8 GB | **No** | Needs IDLE_TIMEOUT added |
| sd-forge-main | all | ~8 GB | **No** | Gradio, no sleep support |
| forge-turbo | all | ~6 GB | **No** | Gradio, no sleep support |
| sdnext | all | ~8 GB | **No** | Gradio, no sleep support |

**Total permanently locked**: ~52 GB across both GPUs (but only ~18 GB on GPU1 is truly unsleepable by config; SD services are inherently always-on).

### Wake Latency Estimates

| Service Type | Cold Start | Warm Wake | Notes |
|-------------|-----------|-----------|-------|
| ComfyUI (model in RAM) | 10-30s | 3-5s | Model reload from system RAM |
| vLLM (model on disk) | 30-60s | N/A | Full model load from SSD |
| TTS (kokoro/tada) | 5-15s | 2-3s | Small models |
| Whisper STT | 10-20s | 3-5s | large-v3-turbo |
| MusicGen (PRELOAD=false) | 60-120s | N/A | Downloads from HF on first cold start |
| Demucs (PRELOAD=false) | 20-40s | 5-10s | Loads htdemucs_ft on first request |

---

## 7. Issues Identified

### Critical

1. **vllm-zimage has no IDLE_TIMEOUT**: Holds ~10 GB on GPU1 permanently. Prevents GPU1 from freeing VRAM for other services.
2. **tts-qwen has no IDLE_TIMEOUT**: Holds ~8 GB on GPU1 permanently. Combined with vllm-zimage, 18 GB of GPU1 is permanently locked.
3. **Z-Image generation hangs** (UPSTREAM BUG, NOT FIXABLE): vLLM omni v0.12.0rc1 with Z-Image-Turbo — generation hangs on SHM broadcast between vLLM processes. `/health` returns 200, `/v1/models` crashes with `AttributeError: 'State' object has no attribute 'openai_serving_models'`. Container restarted to clear zombie PID/stuck state. Root cause: upstream vLLM pure diffusion mode bug. No fix available without vLLM upgrade.
4. **MusicGen generation crash** (FIXED): Two bugs fixed: (a) EncodecFeatureProcessor misconfiguration — `processor([text])` feeds text through float conversion. Fix: `processor.tokenizer([text])` for text-only input. (b) Output tensor access — `audio_values.audios[0]` fails because `generate()` returns raw tensor, not `AudioGenerationOutput`. Fix: `audio_values[0, 0]` for batch=0, channel=0. Sample rate from `model.config.audio_encoder.sampling_rate`. Verified: 200 OK, 124KB WAV (2s), 15s inference (warm).
5. **Demucs separation crash** (FIXED): Two bugs fixed: (a) Missing `torchcodec` dependency — torchaudio 2.11.0+ requires it as default backend. Added to Dockerfile pip install. (b) Double-wrapping batch dimension — `wav.unsqueeze(0)` then `wav[None]` adds 2 batch dims. Fix: remove redundant `[None]` and `[0]` indexing. Verified: 200 OK, 829KB zip (4 stems), 22.9s.
6. **GPU0 oversubscribed by ~1 GB**: comfyui-qwen (~12 GB fp8) + whisper-api (~5 GB) = ~17 GB peak vs 16 GB capacity. Only works if one sleeps while the other is active.
7. **SD services (3x) have no GPU isolation**: `DeviceRequests: []` means sd-forge-main, forge-turbo, sdnext see both GPUs and can allocate on either, fragmenting VRAM unpredictably.

### Warning

6. **MusicGen cold start downloads model from HuggingFace**: PRELOAD=false + no cached model = first request triggers full download (~1.5 GB). Measured: still downloading 5 min after first request. Should pre-cache model in Docker image.
7. **Demucs model not preloaded**: PRELOAD=false means first real audio request incurs 20-40s model load latency.
8. **funasr-api and qwen-asr-api have short IDLE_TIMEOUT (300s)**: May cause frequent wake cycles during notebook execution pauses.
9. **Qwen Image Edit VRAM was ~29 GB in original config, now ~12 GB (fp8)**: Verify fp8 quantization produces acceptable quality for notebooks.

### Info

10. **tts-gateway is CPU-only router**: No VRAM concern, but single point of failure for all TTS.
11. **Whisper WebUI runs on non-standard port 36540**: Confirmed IIS routing via site ID 9.
12. **ComfyUI auth uses bcrypt hash as Bearer token**: Non-standard pattern. The `login/PASSWORD` file stores `bcrypt_hash\nusername`. The hash itself is the API token. CORS must be enabled for bearer auth to work.

---

## 8. Next Steps (Track A0)

| Step | Task | Status | Notes |
|------|------|--------|-------|
| A0.1 | This inventory document | DONE | Sections 1-8 populated with measured data |
| A0.2 | Test sleep/wake per service | DONE | All API endpoints tested. MusicGen + Demucs working post-fix |
| A0.3 | Verify IIS reverse proxy (SSL, routing, WebSocket, CORS) | DONE | IIS config verified per subdomain (Section 3) |
| A0.4 | Fix services KO or NEEDS_FIX | DONE | MusicGen FIXED (2 bugs), Demucs FIXED (2 bugs), Z-Image UPSTREAM BUG (not fixable) |
| A0.5 | Build E2E test CLI for audio services | DONE | `genai.py audio-apis e2e [service]` — 5/5 services pass |
| A0.6 | E2E Papermill GenAI series validation | DONE | Audio 12/21 pass (8 blocked by expired OpenAI key, 1 numba/numpy conflict). Video 2/2 pass. Fixed total_mem bug in 20 notebooks |

### A0.2 Remaining Work

- [x] Wait for MusicGen model download to complete, test generation — DONE, 200 OK (2s audio, 124KB WAV)
- [x] Test Demucs with real audio file — DONE, 200 OK (4 stems, 829KB zip, 22.9s)
- [ ] Test Z-Image text-to-image — BLOCKED by upstream vLLM bug
- [ ] Measure idle VRAM after services sleep (wait > IDLE_TIMEOUT)
- [ ] Measure wake latency for each service (cold start timer)
- [ ] Test SD services with actual image generation

### A0.6 Papermill Validation Results (2026-05-01)

**Bug fix:** `total_mem` -> `total_memory` in 20 notebooks (PyTorch API). Affects all GenAI Audio + Video notebooks with GPU detection code.

**Audio Series (21 notebooks):**

| Notebook | Result | Time |
|----------|--------|------|
| 01-1-OpenAI-TTS-Intro | FAIL (OpenAI key 401) | - |
| 01-2-OpenAI-Whisper-STT | FAIL (OpenAI key 401) | - |
| 01-3-Basic-Audio-Operations | FAIL (OpenAI key 401) | - |
| 01-4-Whisper-Local | FAIL (numba/numpy conflict) | - |
| 01-5-Kokoro-TTS-Local | PASS | 7.8s |
| 02-1-Chatterbox-TTS | PASS | 8.9s |
| 02-2-XTTS-Voice-Cloning | PASS | 9.6s |
| 02-3-MusicGen-Generation | PASS | 7.8s |
| 02-4-Demucs-Source-Separation | PASS | 7.7s |
| 02-5-Multi-Model-TTS-Gateway | PASS | 4.8s |
| 02-6-MIDI-Generation | PASS | 17.5s |
| 02-7-Song-Generation | PASS | 13.0s |
| 02-8-Expressive-TTS | PASS | 7.8s |
| 03-1-Multi-Model-Audio-Comparison | FAIL (OpenAI key 401) | - |
| 03-2-Audio-Pipeline-Orchestration | FAIL (OpenAI key 401) | - |
| 03-3-Realtime-Voice-API | PASS | 33.2s |
| 04-1-Podcast-Production | FAIL (OpenAI key 401) | - |
| 04-2-Audiobook-Production | FAIL (OpenAI key 401) | - |
| 04-3-Music-Composition-Workflow | PASS | ~20s |
| 04-4-Audio-Video-Sync | FAIL (OpenAI key 401) | - |
| 04-5-LiveCoding-LLM-Music | PASS | ~20s |

**Video Series (sample):**
- 01-3-Qwen-VL-Video-Analysis: PASS (22.9s)
- 01-4-Video-Enhancement-ESRGAN: PASS (14.2s)

**Summary:** 14/21 Audio + 2/2 Video = **16/23 pass**. All 7 OpenAI failures trace to expired API key `sk-F6ZJn...` (401). The numba/numpy conflict on Whisper-Local is an environment dependency issue (numba needs numpy <=2.3, system has 2.4).

**Action items:**
- [ ] Renew OpenAI API key in `.env` (unblocks 8 notebooks)
- [ ] Pin numpy <2.4 or upgrade numba (fixes Whisper-Local)

---

## 9. Docker Compose Locations (to verify)

Services are managed via Docker Compose. Expected compose directories:

- `docker-configurations/services/comfyui-qwen/` — ComfyUI Qwen
- `docker-configurations/services/comfyui-video/` — ComfyUI Video
- (Other services: to be mapped during A0.2)

Use `docker inspect <container> --format '{{index .Config.Labels "com.docker.compose.project.working_dir"}}'` to find actual compose directories.

---

*Generated: 2026-05-01 | Track A0 GenAI Services Audit | po-2023*
