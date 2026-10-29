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

# 2. Download model (~11GB safetensors, official snapshot)
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

Mesures du 2026-10-29 sur la RTX 3090 (24 Go) de `po-2023` :

| Poids | VRAM | Source |
|---|---|---|
| fp16 (`--half`, la configuration du compose) | **~20,3 Go** | warm-up mesuré le 2026-10-06 |
| NF4 quantifié | **5,0 Go de fichiers**, cible annoncée « 12 Go+ » | `groxaxo/s2-pro-BnB-4Bits` |

Le `--half` du compose n'aboutit donc pas au « ~12 Go » annoncé auparavant : le service occupe ~20,3 Go, soit la quasi-totalité d'une carte de 24 Go et aucune carte de 16 Go. Arrêter `tts-qwen` ne libère pas 12 Go.

### Checkpoints quantifiés existants

Tailles mesurées via l'API HuggingFace (`?blobs=true`) :

| Dérivé | Total | Remarque |
|---|---|---|
| `groxaxo/s2-pro-BnB-4Bits` | 5,00 Go | NF4 — **exige le fork**, voir ci-dessous |
| `scarxity/fish-speech-s2-pro-nf4` | 5,00 Go | NF4 |
| `baicai1145/s2-pro-w4a16` | 6,13 Go | safetensors |
| `drbaph/s2-pro-fp8` | 8,05 Go | fp8 |

**Piège vérifié** : ajouter `bitsandbytes` et `accelerate` à l'image officielle ne suffit pas. Les deux paquets y sont absents (`ModuleNotFoundError` sur chacun), mais surtout le loader officiel construit des couches fp16 et ne sait pas lire un state dict préquantifié — le model card le dit explicitement : « not a legacy int4 or int8 export », « meant to be loaded through the fork's `bnb4` path ». Il faut `groxaxo/fish-speech-int4-patch`, dont `tools/api_server.py` transmet `bnb4=self.args.bnb4`.

### Sleep

Le sidecar `idle-monitor` **arrête** le conteneur, il ne l'endort pas : au redémarrage, les ~20 Go sont rechargés. Pour un usage ponctuel, c'est ce régime qu'il faut remplacer (cf `.claude/rules/model-quantization-and-sleep.md`).

## Integration

This service integrates with the audiobook pipeline (`04-6-Audiobook-Pipeline.ipynb`) as P4 TTS engine, providing expressive tag support that Kokoro cannot leverage.

Port: 8197 | GPU: 1 (RTX 3090) | Network: host (tts-network bridge optional)
