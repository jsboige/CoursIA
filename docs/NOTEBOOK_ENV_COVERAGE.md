# Notebook Environment Coverage Audit

**Issue**: #1055
**Generated**: 2026-05-14
**Branch**: `chore/env-coverage-audit-1055`
**Scope**: All notebook families in `MyIA.AI.Notebooks/`

---

## Phase 1: Per-Family Inventory

### Legend

| Symbol | Meaning |
|--------|---------|
| KEY | API key or token required |
| URL | Service endpoint URL |
| ENV | Python/conda environment |
| KERNEL | Jupyter kernel type |
| DOCKER | Docker service dependency |
| WSL | Requires WSL (Linux) |

---

### 1. GenAI — Image (38 notebooks)

Path: `MyIA.AI.Notebooks/GenAI/Image/`
Kernel: `python3`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| `COMFYUI_API_URL` | URL | `.env` | `https://qwen-image-edit.myia.io` (or `localhost:8188`) |
| `COMFYUI_API_TOKEN` / `COMFYUI_AUTH_TOKEN` / `QWEN_API_TOKEN` | KEY | `.env` | Bearer token for ComfyUI |
| `ZIMAGE_API_URL` / `ZIMAGE_API_BASE` | URL | `.env` | `https://z-image.myia.io` (Lumina/vLLM) |
| `SD_FORGE_API_URL` / `FORGE_API_URL` / `SD_BASE_URL` | URL | `.env` | SD Forge + Turbo variants |
| `SD_FORGE_TURBO_URL` | URL | `.env` | Turbo variant |
| `SDNEXT_API_URL` | URL | `.env` | SD.Next alternative |
| `FORGE_USER` / `FORGE_PASSWORD` | KEY | `.env` | SD Forge credentials |
| `OPENAI_API_KEY` | KEY | `.env` | DALL-E, GPT Vision |
| `OPENAI_CHAT_MODEL_ID` | KEY | `.env` | Default `gpt-5-mini` |
| `DEFAULT_VISION_MODEL` | KEY | `.env` | Default `gpt-5o-mini` |
| `DEFAULT_IMAGE_MODEL` | KEY | `.env` | Default `gpt-5o-mini` |
| `BATCH_MODE` | ENV | `.env` | `true` for Papermill |

**Docker services on po-2023**: qwen-image-edit (8188), z-image (8001), sd-forge-turbo (17861), sd-forge (7860), sdnext (7861)

---

### 2. GenAI — Audio (42 notebooks)

Path: `MyIA.AI.Notebooks/GenAI/Audio/`
Kernel: `python3`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| `WHISPER_API_URL` | URL | `.env` | `https://whisper-api.myia.io` (faster-whisper) |
| `WHISPER_API_KEY` | KEY | `.env` | Whisper API auth |
| `OPENAI_STT_MODEL` | KEY | `.env` | Fallback `whisper-1` |
| `TTS_API_URL` | URL | `.env` | `https://tts-api.myia.io` (gateway) |
| `TTS_API_KEY` | KEY | `.env` | TTS gateway auth |
| `KOKORO_TTS_URL` | KEY | `.env` | Kokoro endpoint |
| `TADA_TTS_URL` | KEY | `.env` | TADA 3B ML endpoint |
| `QWEN_TTS_URL` | KEY | `.env` | Qwen3 TTS endpoint |
| `TTS_DEFAULT_MODEL` | KEY | `.env` | Default `kokoro` |
| `OPENAI_TTS_MODEL` / `OPENAI_TTS_VOICE` | KEY | `.env` | OpenAI fallback |
| `MUSICGEN_API_URL` | URL | `.env` | `https://musicgen-api.myia.io` |
| `MUSICGEN_API_KEY` | KEY | `.env` | MusicGen auth |
| `DEMUCS_API_URL` | URL | `.env` | `https://demucs-api.myia.io` |
| `DEMUCS_API_KEY` | KEY | `.env` | Demucs auth |
| `QWEN_ASR_API_KEY` | KEY | `docker-configurations/services/qwen-asr-api/.env` | Qwen ASR auth (NOT in GenAI/.env) |
| `FUNASR_API_KEY` | KEY | `docker-configurations/services/funasr-api/.env` | FunASR auth (NOT in GenAI/.env) |
| `AUDIO_OUTPUT_DIR` | ENV | `.env` | `outputs/audio` |
| `BATCH_MODE` | ENV | `.env` | `true` for Papermill |

**Docker services on po-2023**: whisper-api (8190), tts-api (8196), musicgen-api (8192), demucs-api (8193), kokoro-tts (8191), qwen-asr-api (8195)

**Note**: Qwen ASR + FunASR keys are in `docker-configurations/services/{qwen-asr-api,funasr-api}/.env`, NOT in GenAI `.env`.

---

### 3. GenAI — Video (32 notebooks)

Path: `MyIA.AI.Notebooks/GenAI/Video/`
Kernel: `python3`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| `COMFYUI_VIDEO_URL` | URL | `.env` | `https://comfyui-video.myia.io` |
| `COMFYUI_VIDEO_TOKEN` | KEY | `.env` | Bearer token |
| `COMFYUI_VIDEO_TIMEOUT` | ENV | `.env` | Default 600s |
| `OPENAI_API_KEY` | KEY | `.env` | Sora access |
| `VIDEO_OUTPUT_DIR` | ENV | `.env` | `outputs/video` |
| `HUNYUANVIDEO_QUANTIZE` | ENV | `.env` | INT8 quantization |
| `WAN_QUANTIZE` | ENV | `.env` | Quantization for Wan 2.1/2.2 |
| `BATCH_MODE` | ENV | `.env` | `true` for Papermill |

**Docker services on po-2023**: comfyui-video (8189)

---

### 4. GenAI — Texte (18 notebooks)

Path: `MyIA.AI.Notebooks/GenAI/Texte/`
Kernel: `python3`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| `OPENAI_API_KEY` | KEY | `.env` | GPT models |
| `OPENAI_BASE_URL` | URL | `.env` | Optional (OpenRouter) |
| `OPENAI_CHAT_MODEL_ID` | KEY | `.env` | Default `gpt-5-mini` |
| `ANTHROPIC_API_KEY` | KEY | `.env` | Claude models |
| `ANTHROPIC_CHAT_MODEL_ID` | KEY | `.env` | Default `claude-sonnet-4-5` |
| `OPENROUTER_API_KEY` | KEY | `.env` | Multi-model access |
| `GLOBAL_LLM_SERVICE` | ENV | `.env` | Default `OpenAI` |
| `QDRANT_URL` | URL | `.env` | `https://qdrant.myia.io` |
| `QDRANT_API_KEY` | KEY | `.env` | Qdrant auth |
| `GITHUB_TOKEN` | KEY | `.env` | LeanDojo |
| `BATCH_MODE` | ENV | `.env` | `true` for Papermill |

---

### 5. SymbolicAI — Lean (notebooks)

Path: `MyIA.AI.Notebooks/SymbolicAI/Lean/`
Kernel: `lean4` or `python3` (WSL)

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| Lean 4 toolchain (`elan`) | ENV | System | `lean --version` |
| WSL with Lean kernel | KERNEL | System | WSL required |
| `GITHUB_TOKEN` | KEY | `.env` or system | For LeanDojo |
| Mathlib cache | ENV | System | `~/.cache/lean` |

---

### 6. SymbolicAI — SemanticWeb (notebooks)

Path: `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/`
Kernel: `python3` or `.net-csharp`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| `rdflib`, `owlready2`, `reasonable`, `pyshacl` | ENV | Conda `epita_symbolic_ai` | Python packages |
| .NET 9.0 SDK | ENV | System | C# notebooks |
| `dotnet-interactive` | KERNEL | System | Jupyter kernel |

---

### 7. SymbolicAI — SmartContract (notebooks)

Path: `MyIA.AI.Notebooks/SymbolicAI/SmartContract/`
Kernel: `python3` or `.net-csharp`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| `web3`, `solcx`, `eth-tester` | ENV | pip | Python packages |
| Foundry/Anvil | DOCKER | System | Local blockchain |
| .NET 9.0 SDK | ENV | System | C# notebooks |
| `ANTHROPIC_API_KEY` | KEY | `GenAI/.env` | LLM-assisted SC |
| `OPENAI_API_KEY` | KEY | `GenAI/.env` | LLM-assisted SC |
| `OPENROUTER_API_KEY` | KEY | `GenAI/.env` | Free models fallback |
| `ZAI_API_KEY` | KEY | `.env` | SymbolicAI lib |
| `QWEN_LOCAL_API_KEY` | KEY | `.env` | Local Qwen endpoint |

---

### 8. SymbolicAI — Planning / Tweety (notebooks)

Path: `MyIA.AI.Notebooks/SymbolicAI/{Planning,Tweety}/`
Kernel: `.net-csharp`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| .NET 9.0 SDK | ENV | System | Required |
| `dotnet-interactive` | KERNEL | System | Jupyter kernel |
| TweetyLib JARs | ENV | NuGet/packages | Java bridge for Tweety |

---

### 9. Search (notebooks)

Path: `MyIA.AI.Notebooks/Search/`
Kernel: `python3` or `.net-csharp`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| `ortools` | ENV | pip | Google OR-Tools |
| `z3-solver` | ENV | pip | Z3 theorem prover |
| .NET 9.0 SDK | ENV | System | C# notebooks |
| `dotnet-interactive` | KERNEL | System | Jupyter kernel |

No API keys required.

---

### 10. Sudoku (notebooks)

Path: `MyIA.AI.Notebooks/Sudoku/`
Kernel: `.net-csharp`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| .NET 9.0 SDK | ENV | System | Required |
| `dotnet-interactive` | KERNEL | System | Jupyter kernel |

No API keys required.

---

### 11. ML (notebooks)

Path: `MyIA.AI.Notebooks/ML/`
Kernel: `.net-csharp`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| .NET 9.0 SDK | ENV | System | Required |
| `dotnet-interactive` | KERNEL | System | Jupyter kernel |
| `Microsoft.ML` | ENV | NuGet | ML.NET packages |
| `ANTHROPIC_API_KEY` | KEY | `GenAI/.env` | Some ML notebooks |
| `OPENAI_API_KEY` | KEY | `GenAI/.env` | Some ML notebooks |

---

### 12. Probas / Infer.NET (notebooks)

Path: `MyIA.AI.Notebooks/Probas/`
Kernel: `.net-csharp`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| .NET 9.0 SDK | ENV | System | Required |
| `dotnet-interactive` | KERNEL | System | Jupyter kernel |
| `Microsoft.ML.Probabilistic` | ENV | NuGet | Infer.NET compiler |

No API keys required.

---

### 13. GameTheory (notebooks)

Path: `MyIA.AI.Notebooks/GameTheory/`
Kernel: `python3` (WSL) — requires OpenSpiel

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| WSL with Python | KERNEL | System | Required |
| `open_spiel` | ENV | WSL pip | Built from source |
| `nashpy` | ENV | pip | Nash equilibria |
| WSL kernel `Python (GameTheory WSL + OpenSpiel)` | KERNEL | Jupyter | Custom kernelspec |

No API keys required.

---

### 14. IIT — PyPhi (notebooks)

Path: `MyIA.AI.Notebooks/IIT/`
Kernel: `python3`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| `pyphi` | ENV | pip | Integrated Information Theory |
| Python 3.10+ | ENV | System | Required |

No API keys required.

---

### 15. QuantConnect (27 notebooks + 50 strategies)

Path: `MyIA.AI.Notebooks/QuantConnect/`
Kernel: `python3`

| Variable / Dependency | Type | Source | Notes |
|-----------------------|------|--------|-------|
| `QC_API_USER_ID` | KEY | `Config/settings.json` | QC Cloud API |
| `QC_API_ACCESS_TOKEN` | KEY | `Config/settings.json` | QC Cloud API |
| `OPENAI_API_KEY` | KEY | `GenAI/.env` | LLM-assisted strategies |
| `ANTHROPIC_API_KEY` | KEY | `GenAI/.env` | LLM-assisted strategies |
| `HUGGINGFACE_TOKEN` | KEY | `GenAI/.env` | HF models |
| `NEWSAPI_KEY` | KEY | `.env` or settings | News data |
| `TIINGO_API_KEY` | KEY | `.env` or settings | Market data |
| `ALPHAVANTAGE_API_KEY` | KEY | `.env` or settings | Market data |

---

## Phase 2: Agent x Family Matrix

### po-2023 Capability Matrix

po-2023 = GenAI host machine (2 GPUs: 3080Ti 16GB + 3090 24GB).

| Family | Kernel | API Keys | Docker/Local | .env | Can Execute? | Blockers |
|--------|--------|----------|--------------|------|-------------|----------|
| GenAI/Image | python3 | COMFYUI, ZIMAGE, SD_FORGE, OPENAI | 5 Docker services UP | `.env` | YES | None |
| GenAI/Audio | python3 | WHISPER, TTS, MUSICGEN, DEMUCS | 6 Docker services UP | `.env` | YES | None |
| GenAI/Video | python3 | COMFYUI_VIDEO, OPENAI | 1 Docker service UP | `.env` | YES | None |
| GenAI/Texte | python3 | OPENAI, ANTHROPIC, OPENROUTER, QDRANT | Cloud only | `.env` | YES | None |
| SymbolicAI/Lean | lean4/WSL | GITHUB_TOKEN | System | — | PARTIAL | elan 4.2.1 installed, WSL Lean kernel needed |
| SymbolicAI/SemanticWeb | python3 + .net-csharp | None | pip packages | — | YES | None (conda env `epita_symbolic_ai` installed) |
| SymbolicAI/SmartContract | python3 + .net-csharp | OPENAI, ANTHROPIC, OPENROUTER | Foundry/Anvil | `GenAI/.env` | PARTIAL | Anvil needed for local blockchain |
| SymbolicAI/Planning | .net-csharp | None | NuGet | — | YES | None (.NET 9.0 + kernels installed) |
| SymbolicAI/Tweety | .net-csharp | None | NuGet | — | YES | None (.NET 9.0 + kernels installed) |
| Search | python3 + .net-csharp | None | ortools OK, z3 OK | — | YES | None |
| Sudoku | .net-csharp | None | NuGet | — | YES | None (.NET 9.0 + kernels installed) |
| ML | .net-csharp | OPENAI, ANTHROPIC | NuGet | `GenAI/.env` | YES | None (.NET 9.0 + kernels installed) |
| Probas | .net-csharp | None | NuGet | — | YES | None (.NET 9.0 + kernels installed) |
| GameTheory | python3 (WSL) | None | open_spiel | — | PARTIAL | OpenSpiel 1.6.14 installed in ~/coursia-venv, WSL kernel registration needed |
| IIT | python3 | None | pyphi 1.2.0 | — | YES | None (pyphi installed) |
| QuantConnect | python3 | QC_API, OPENAI, ANTHROPIC, HF | Cloud | `Config/settings.json` + `.env` | YES | None |

### Summary: po-2023 Coverage (updated 2026-05-14, verified)

| Status | Families | Count |
|--------|----------|-------|
| **FULL** | GenAI (Image, Audio, Video, Texte), QuantConnect, Planning, Tweety, Sudoku, ML, Probas, Search, IIT, SemanticWeb | 12 |
| **PARTIAL** | Lean (WSL kernel), SmartContract (anvil), GameTheory (OpenSpiel) | 3 |
| **NO** | — | 0 |

**Verified installed on po-2023**:
- .NET SDKs: 8.0.319, 8.0.421, **9.0.205, 9.0.314**, 10.0.108
- dotnet-interactive: 1.0.707101 (Jupyter kernels: `.net-csharp`, `.net-fsharp`, `.net-powershell`)
- Python packages: ortools, z3-solver, pyphi 1.2.0
- WSL: Ubuntu (running)

**Remaining gaps**: WSL kernel registration (GameTheory + Lean), anvil (SmartContract local blockchain).

---

## Phase 3: Missing Items + Distribution Plan

### Critical Installs for po-2023

| Priority | Install | Families Unlocked | Effort | Status |
|----------|---------|-------------------|--------|--------|
| ~~P0~~ | ~~.NET 9.0 SDK~~ | ~~Sudoku, ML, Probas, Planning, Tweety, Search(C#), SemanticWeb(C#), SmartContract(C#)~~ | ~30 min | DONE (9.0.205 + 9.0.314) |
| ~~P0~~ | ~~`dotnet-interactive` + Jupyter kernels~~ | ~~Same as above~~ | ~10 min | DONE (1.0.707101) |
| ~~P1~~ | ~~`pyphi`~~ | ~~IIT~~ | ~5 min | DONE (1.2.0) |
| ~~P1~~ | ~~Conda env `epita_symbolic_ai`~~ | ~~SemanticWeb(Python)~~ | ~20 min | DONE (rdflib 7.6.0, owlready2 0.50, reasonable 0.4.1, pyshacl 0.31.0) |
| ~~P2~~ | ~~OpenSpiel in WSL Ubuntu~~ | ~~GameTheory~~ | ~10 min (pip) | DONE (open-spiel 1.6.14 in ~/coursia-venv) |
| ~~P2~~ | ~~`elan` (Lean toolchain)~~ | ~~Lean~~ | ~15 min | DONE (elan 4.2.1, Lean 4.29.1) |

### API Key Distribution

| Key | Source | Destination Families | Already in GenAI/.env? |
|-----|--------|---------------------|----------------------|
| `OPENAI_API_KEY` | GenAI/.env | Texte, Video, ML, SmartContract, QuantConnect | YES |
| `ANTHROPIC_API_KEY` | GenAI/.env | Texte, ML, SmartContract, QuantConnect | YES |
| `OPENROUTER_API_KEY` | GenAI/.env | Texte, SmartContract | YES |
| `GITHUB_TOKEN` | GenAI/.env | Lean, Texte | YES |
| `QC_API_USER_ID` | Config/settings.json | QuantConnect only | N/A (separate config) |
| `QC_API_ACCESS_TOKEN` | Config/settings.json | QuantConnect only | N/A |
| `NEWSAPI_KEY` | Per-notebook | QuantConnect | NO — separate |
| `TIINGO_API_KEY` | Per-notebook | QuantConnect | NO — separate |
| `ALPHAVANTAGE_API_KEY` | Per-notebook | QuantConnect | NO — separate |
| `HUGGINGFACE_TOKEN` | GenAI/.env | QuantConnect, GenAI/Image | YES |
| `ZAI_API_KEY` | SymbolicAI/.env | SmartContract | NO — separate |
| `QWEN_LOCAL_API_KEY` | SymbolicAI/.env | SmartContract | NO — separate |
| `QWEN_ASR_API_KEY` | docker .env | Audio (ASR notebooks) | NO — `docker-configurations/services/qwen-asr-api/.env` |

### Recommended Distribution Strategy

1. **GenAI/.env = primary key store** for all cloud API keys (OpenAI, Anthropic, OpenRouter, GitHub)
2. **Config/settings.json = QuantConnect** specific (QC_API_USER_ID, QC_API_ACCESS_TOKEN)
3. **Docker service .env = service-specific keys** (Qwen ASR, FunASR, ComfyUI)
4. **Per-family .env = niche keys** (ZAI_API_KEY for SymbolicAI, market data keys for QC)
5. **Machine-level env vars = runtime** (CUDA_VISIBLE_DEVICES, PYTHONPATH)

---

## Action Items

- [x] Install .NET 9.0 SDK on po-2023 (9.0.205 + 9.0.314 already present)
- [x] Install `dotnet-interactive` + register Jupyter kernels (1.0.707101)
- [x] Install `pyphi` for IIT notebooks (1.2.0)
- [x] Create conda env `epita_symbolic_ai` on po-2023 (SemanticWeb Python — rdflib 7.6.0, owlready2 0.50)
- [x] Build OpenSpiel in WSL Ubuntu (open-spiel 1.6.14 in ~/coursia-venv)
- [x] Install `elan` Lean toolchain (elan 4.2.1, Lean 4.29.1)
- [ ] Consolidate API key documentation (which .env for which key)
- [ ] Add FunASR/Qwen ASR keys to GenAI/.env (or document the split clearly)
- [ ] Regenerate this document after each infrastructure change
