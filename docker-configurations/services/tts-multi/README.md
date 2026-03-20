# Multi-Model TTS Service

OpenAI-compatible TTS API with 3 models: Kokoro, TADA 3B ML, and Qwen3 TTS.

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Gateway (Port 8196)                      │
│  Routes requests to appropriate model based on path prefix  │
└─────────────────────────────────────────────────────────────┘
           │                    │                    │
           ▼                    ▼                    ▼
    ┌──────────┐         ┌──────────┐         ┌──────────┐
    │ Kokoro   │         │   TADA   │         │  Qwen3   │
    │  :8000   │         │  :8000   │         │  :8000   │
    │ Internal │         │ Internal │         │ Internal │
    └──────────┘         └──────────┘         └──────────┘
```

## Path Routing

| Path | Model | Description |
|------|-------|-------------|
| `/v1/audio/speech` | Kokoro | Default, backward compatible |
| `/tada/v1/audio/speech` | TADA 3B ML | HumeAI's advanced TTS |
| `/qwen/v1/audio/speech` | Qwen3 TTS | Qwen's high-quality TTS |

## Models

### Kokoro TTS
- **Model**: Kokoro v0.19
- **VRAM**: ~2GB
- **Speed**: Fast
- **Voices**: 6 (af_sky, am_adam, af_bella, am_michael, af_nova, af_sarah)

### TADA 3B ML
- **Model**: HumeAI/tada-3b-ml
- **VRAM**: ~6GB
- **Speed**: Medium
- **Voices**: 1 (default)

### Qwen3 TTS
- **Model**: Qwen/Qwen3-TTS-12Hz-1.7B-CustomVoice
- **VRAM**: ~4GB
- **Speed**: Medium
- **Voices**: Multiple (default, female, male, custom1-3)

## Setup

1. **Copy environment file**:
   ```bash
   cp .env.example .env
   ```

2. **Edit .env** to configure GPU IDs and paths:
   ```bash
   KOKORO_GPU_ID=1
   TADA_GPU_ID=1
   QWEN_GPU_ID=1
   ```

3. **Start services**:
   ```bash
   docker-compose up -d
   ```

4. **Check status**:
   ```bash
   docker-compose ps
   docker-compose logs -f
   ```

## Usage Examples

### Using Kokoro (default)
```python
import requests

response = requests.post(
    "http://localhost:8196/v1/audio/speech",
    json={
        "model": "kokoro",
        "input": "Hello, world!",
        "voice": "alloy"
    }
)

with open("kokoro_speech.wav", "wb") as f:
    f.write(response.content)
```

### Using TADA
```python
response = requests.post(
    "http://localhost:8196/tada/v1/audio/speech",
    json={
        "model": "tada",
        "input": "Hello, world!",
        "voice": "alloy"
    }
)
```

### Using Qwen3
```python
response = requests.post(
    "http://localhost:8196/qwen/v1/audio/speech",
    json={
        "model": "qwen3",
        "input": "Hello, world!",
        "voice": "alloy"
    }
)
```

## API Endpoints

### Gateway (Port 8196)

- `GET /health` - Health check
- `GET /v1/models` - List available models
- `GET /v1/voices` - List available voices
- `POST /v1/audio/speech` - Generate speech (Kokoro)
- `POST /tada/v1/audio/speech` - Generate speech (TADA)
- `POST /qwen/v1/audio/speech` - Generate speech (Qwen3)

### Individual Services (Internal, Port 8000)

Each TTS service exposes the same endpoints internally:
- `GET /health` - Service health check
- `GET /v1/models` - Model info
- `GET /v1/voices` - Available voices
- `POST /v1/audio/speech` - Generate speech

## GPU Allocation

Default configuration (adjust in .env):
- All models on GPU 1 (RTX 3090, 24GB)
- Total VRAM: ~12GB (Kokoro 2GB + TADA 6GB + Qwen3 4GB)

For separate GPUs:
```bash
KOKORO_GPU_ID=0  # RTX 3080 Ti, 16GB
TADA_GPU_ID=1    # RTX 3090, 24GB
QWEN_GPU_ID=1    # RTX 3090, 24GB
```

## Model Management

### Lazy Loading
Models are loaded on first request and unloaded after idle timeout (default: 1200s).

### Preload All Models
Set `PRELOAD_MODEL=true` in .env to load all models on startup.

### Adjust Idle Timeout
```bash
IDLE_TIMEOUT=1800  # 30 minutes
```

## Troubleshooting

### Check GPU Usage
```bash
nvidia-smi
```

### View Logs
```bash
docker-compose logs -f tts-gateway
docker-compose logs -f tts-kokoro
docker-compose logs -f tts-tada
docker-compose logs -f tts-qwen
```

### Restart Services
```bash
docker-compose restart tts-gateway
docker-compose restart tts-tada
docker-compose restart tts-qwen
```

### Rebuild Services
```bash
docker-compose up -d --build
```

## Integration with Notebooks

Update `MyIA.AI.Notebooks/GenAI/Audio/.env`:
```bash
# Multi-Model TTS Gateway
TTS_API_URL=http://localhost:8196
TTS_API_MODELS=kokoro,tada,qwen3

# Model-specific endpoints (optional)
KOKORO_TTS_URL=http://localhost:8196/v1/audio/speech
TADA_TTS_URL=http://localhost:8196/tada/v1/audio/speech
QWEN_TTS_URL=http://localhost:8196/qwen/v1/audio/speech
```

## Voice Mapping

| OpenAI Voice | Kokoro | TADA | Qwen3 |
|--------------|--------|------|-------|
| alloy | af_sky | default | default |
| echo | am_adam | default | female |
| fable | af_bella | default | male |
| onyx | am_michael | default | custom1 |
| nova | af_nova | default | custom2 |
| shimmer | af_sarah | default | custom3 |
