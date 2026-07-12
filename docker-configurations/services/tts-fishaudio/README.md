# FishAudio S2-Pro TTS Service

Expressive TTS with 15000+ prosodic tags, Dual-AR architecture (Slow 4B + Fast 400M), 80+ languages.

## Requirements

- NVIDIA GPU with 24GB VRAM (RTX 3090+)
- Docker + NVIDIA Container Toolkit
- HuggingFace token (for model download)

## Setup

```bash
# 1. Copy configuration
cp .env.example .env
# Edit .env with your HuggingFace token

# 2. Download model (~8GB)
docker run --rm -v $(pwd)/checkpoints:/app/checkpoints \
  -e HF_TOKEN=your_token \
  fishaudio/fish-speech:latest \
  python -c "from huggingface_hub import snapshot_download; snapshot_download('fishaudio/s2-pro', local_dir='/app/checkpoints/s2-pro')"

# 3. Start service
docker compose up -d

# 4. Verify
curl http://localhost:8197/v1/health
```

## API Usage

### Generate speech

```python
import requests

response = requests.post("http://localhost:8197/v1/tts", json={
    "text": "[whisper] Bonjour tout le monde",
    "reference_id": None,  # Optional: speaker reference
})

with open("output.wav", "wb") as f:
    f.write(response.content)
```

### With voice reference

```python
response = requests.post("http://localhost:8197/v1/tts", json={
    "text": "[shout] Jamais ! cria-t-elle.",
    "reference_id": "narrator_male",  # From references/ directory
})
```

## Expressive Tags

FishAudio S2-Pro supports inline tags in text:
- `[whisper]`, `[shout]`, `[laugh]`, `[pause]`, `[breath]`
- `[cold]`, `[timid]`, `[indignant]`, `[onctuous]`
- `[professional broadcast tone]`, `[slow]`, `[fast]`
- 15000+ tags for fine-grained prosody control

## VRAM Management

Full inference requires ~24GB. Options:
- `--half` flag (default): fp16, reduces to ~12GB
- Stop `tts-qwen` container to free additional VRAM on GPU1
- Use quantized model if available

## Integration

This service integrates with the audiobook pipeline (`04-6-Audiobook-Pipeline.ipynb`) as P4 TTS engine, providing expressive tag support that Kokoro cannot leverage.

Port: 8197 | GPU: 1 (RTX 3090) | Network: host (tts-network bridge optional)
