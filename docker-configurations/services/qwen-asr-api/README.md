# Qwen ASR API - Multilingual Speech-to-Text

Service FastAPI exposant une API OpenAI-compatible pour la transcription audio multilingue avec Qwen3-ASR-1.7B.

## Vue d'ensemble

| Parametre | Valeur |
|-----------|--------|
| **Modele** | Qwen/Qwen3-ASR-1.7B |
| **Forced Aligner** | Qwen/Qwen3-ForcedAligner-0.6B (timestamps mot-niveau) |
| **Port** | 8195 (configurable via `QWEN_ASR_PORT`) |
| **GPU** | GPU 1 (RTX 3090, 24GB) |
| **VRAM** | ~4GB |
| **API** | OpenAI `/v1/audio/transcriptions` compatible |
| **Langues** | 52 langues auto-detectees (FR, EN, DE, ES, ZH, JA, KO, AR, etc.) |
| **Idle timeout** | 300s (dechargement automatique du modele) |
| **URL cloud** | `https://stt.myia.io/qwen` |

## Demarrage

```bash
# Configuration
cp .env.example .env
# Editer .env : ajouter HF_TOKEN (modele gated)

# Build et demarrage
docker-compose up -d --build

# Verification
curl http://localhost:8195/health
```

## API Endpoints

### Health Check

```bash
curl http://localhost:8195/health
```

### Transcription (OpenAI-compatible)

```bash
# Transcription simple (auto-detection langue)
curl -X POST http://localhost:8195/v1/audio/transcriptions \
  -F "file=@audio.mp3" \
  -F "model=qwen-asr-1"

# Avec indication de langue (ISO 639-1 supporte)
curl -X POST http://localhost:8195/v1/audio/transcriptions \
  -F "file=@audio.mp3" \
  -F "model=qwen-asr-1" \
  -F "language=fr"

# Format verbose avec timestamps
curl -X POST http://localhost:8195/v1/audio/transcriptions \
  -F "file=@audio.mp3" \
  -F "model=qwen-asr-1" \
  -F "response_format=verbose_json" \
  -F "timestamp_granularities[]=word"
```

### Liste des modeles

```bash
curl http://localhost:8195/v1/models
```

### Dechargement force (admin)

```bash
curl -X POST http://localhost:8195/admin/unload
```

## Parametres supportes

| Parametre | Type | Defaut | Description |
|-----------|------|--------|-------------|
| `file` | File | (requis) | Fichier audio (mp3, wav, ogg, flac, m4a, webm) |
| `model` | string | `qwen-asr-1` | ID du modele |
| `language` | string | auto | Code ISO 639-1 (`fr`, `en`, `de`...) ou nom complet |
| `response_format` | string | `json` | `json`, `text`, `verbose_json` |
| `timestamp_granularities` | list | `["segment"]` | `["word"]` ou `["segment"]` |
| `temperature` | float | `0.0` | Temperature de generation |

## Normalisation des langues

Le service accepte les codes ISO 639-1 (`fr`, `en`, `de`, `es`...) et les normalise
automatiquement vers les noms complets attendus par le modele (`French`, `English`, etc.).

Codes supportes : zh, en, fr, de, es, pt, it, ko, ja, ru, ar, hi, tr, th, vi, id, ms,
nl, sv, da, fi, pl, cs, fil, fa, el, ro, hu, mk, yue (30 codes + variantes).

## Configuration (.env)

| Variable | Defaut | Description |
|----------|--------|-------------|
| `QWEN_ASR_PORT` | 8195 | Port d'ecoute |
| `GPU_DEVICE_ID` | 1 | ID du GPU nvidia |
| `QWEN_ASR_MODEL` | Qwen/Qwen3-ASR-1.7B | Modele ASR |
| `QWEN_ASR_DTYPE` | bfloat16 | Precision (float16, bfloat16, float32) |
| `FORCED_ALIGNER` | Qwen/Qwen3-ForcedAligner-0.6B | Modele d'alignement (vide = desactive) |
| `PRELOAD_MODEL` | false | Charger le modele au demarrage |
| `IDLE_TIMEOUT` | 300 | Secondes avant dechargement automatique |
| `MAX_FILE_SIZE` | 52428800 | Taille max fichier (50MB) |
| `QWEN_ASR_API_KEY` | (vide) | Cle API bearer token |
| `HF_TOKEN` | (vide) | Token HuggingFace pour modeles gates |

## Architecture

- **Lazy loading** : Le modele est charge a la premiere requete, decharge apres 300s d'inactivite
- **Shared modules** : `../shared/` monte en lecture seule (`lazy_model.py`, `auth_middleware.py`)
- **FFmpeg** : Conversion automatique en WAV 16kHz mono
- **CUDA fallback** : Bascule sur CPU si CUDA indisponible

## Fichiers

```
qwen-asr-api/
├── app.py              # Application FastAPI
├── Dockerfile          # Image CUDA 12.1 + Python 3.11
├── docker-compose.yml  # Orchestration Docker
├── start.sh            # Script de demarrage uvicorn
├── .env.example        # Template configuration
├── .gitignore          # Exclut .env et models/
└── README.md           # Ce fichier
```
