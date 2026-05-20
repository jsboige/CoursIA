# Integration ASR - Transcription Vocale pour Agents IA

## Vue d'ensemble

L'integration ASR (Automatic Speech Recognition) permet aux agents IA de traiter des messages vocaux. Le pipeline utilise un endpoint Whisper heberge sur l'infrastructure locale.

## Architecture

```
Telegram (message vocal .ogg)
  → NanoClaw
    → Conversion format (si necessaire)
    → POST whisper-api.myia.io/v1/audio/transcriptions
    → Texte transcrit
  → LLM (traitement du texte)
  → Reponse Telegram
```

## Endpoint ASR

**URL** : `https://whisper-api.myia.io/v1/audio/transcriptions`

**Model** : faster-whisper large-v3-turbo

**Host** : po-2023 (RTX 3090, ~5GB VRAM)

**Compatibilite** : API compatible OpenAI Whisper

### Formats supportes

| Format | Extension | Note |
|--------|-----------|------|
| OGG Opus | `.ogg` | Format natif Telegram |
| WAV PCM | `.wav` | Non compresse |
| MP3 | `.mp3` | Comprime |
| FLAC | `.flac` | Sans perte |
| M4A | `.m4a` | Apple |

### Parametres

| Parametre | Type | Default | Description |
|-----------|------|---------|-------------|
| `file` | binary | requis | Fichier audio |
| `model` | string | `large-v3-turbo` | Modele Whisper |
| `language` | string | auto | Code langue (fr, en, ...) |
| `response_format` | string | `json` | json, text, srt, vtt |
| `temperature` | float | 0 | Temperature de decodage |

### Exemples

**cURL :**

```bash
curl -X POST https://whisper-api.myia.io/v1/audio/transcriptions \
  -F "file=@message_vocal.ogg" \
  -F "model=large-v3-turbo" \
  -F "language=fr"
```

**Python :**

```python
import requests

def transcribe(audio_path: str, language: str = "fr") -> str:
    response = requests.post(
        "https://whisper-api.myia.io/v1/audio/transcriptions",
        files={"file": open(audio_path, "rb")},
        data={"model": "large-v3-turbo", "language": language},
        timeout=30
    )
    response.raise_for_status()
    return response.json()["text"]
```

**Reponse :**

```json
{
  "text": "Bonjour, peux-tu me resumer les dernieres nouvelles ?",
  "language": "fr",
  "duration": 3.2
}
```

## Integration dans un agent

### Pattern recommande

```python
async def handle_voice_message(audio_bytes: bytes, format: str = "ogg") -> str:
    """Transcrit un message vocal via l'ASR."""
    files = {"file": (f"voice.{format}", audio_bytes)}
    data = {"model": "large-v3-turbo", "language": "fr"}

    async with httpx.AsyncClient() as client:
        response = await client.post(
            ASR_ENDPOINT,
            files=files,
            data=data,
            timeout=30.0
        )
        response.raise_for_status()
        return response.json()["text"]
```

### Gestion d'erreur

```python
async def safe_transcribe(audio_bytes: bytes) -> str | None:
    try:
        text = await handle_voice_message(audio_bytes)
        return text
    except httpx.TimeoutException:
        return "[Transcription indisponible - timeout]"
    except httpx.HTTPStatusError as e:
        return f"[Erreur ASR: {e.response.status_code}]"
    except Exception:
        return "[Transcription echouee]"
```

## Performance

| Duree audio | Latence transcription | Qualite (FR) |
|-------------|----------------------|---------------|
| 5s | ~1s | Excellente |
| 30s | ~3s | Bonne |
| 60s | ~5s | Bonne |
| 5min | ~20s | Correcte |

**Notes** :
- Le modele large-v3-turbo offre un bon compromis vitesse/qualite
- Les messages courts (< 10s) peuvent avoir une qualité reduite
- Le francais est bien supporte (modele entraine sur des donnees multilingues)

## Monitoring

Verifier la sante du service :

```bash
# Health check basique
curl -s https://whisper-api.myia.io/health

# Test fonctionnel
curl -X POST https://whisper-api.myia.io/v1/audio/transcriptions \
  -F "file=@test.wav" -F "model=large-v3-turbo"
```

## Voir aussi

- [Architecture NanoClaw](NanoClaw-Architecture.md)
- [Guide de deploiement](NanoClaw-Deploy.md)
- [GenAI Audio](../../Audio/) — Notebooks sur le traitement audio
