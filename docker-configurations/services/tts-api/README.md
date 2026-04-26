# TTS API - Text-to-Speech (Kokoro)

API OpenAI-compatible pour la synthese vocale, basee sur le modele Kokoro v0.19.

| Champ | Valeur |
|-------|--------|
| Modele | kokoro-v0_19 |
| Port | 8191 |
| GPU | GPU 1, RTX 3090 (24 GB) |
| VRAM | ~2 GB |
| API | OpenAI `/v1/audio/speech` compatible |
| Idle timeout | 300 s (default), 1200 s (prod) |
| URL cloud | `https://tts-api.myia.io` |

## Demarrage

```bash
# Build et lancement
docker compose up -d --build

# Image pre-build (hybride)
docker compose -f docker-compose-hybrid.yml up -d

# Logs
docker compose logs -f tts-api
```

## Endpoints API

### Health check

```bash
curl http://localhost:8191/health
```

### Synthese vocale

```bash
curl -X POST http://localhost:8191/v1/audio/speech \
  -H "Authorization: Bearer $TTS_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "input": "Bonjour, bienvenue sur le service de synthese vocale.",
    "voice": "alloy",
    "response_format": "mp3",
    "speed": 1.0
  }' --output speech.mp3
```

### Liste des voix

```bash
curl http://localhost:8191/v1/voices
```

### Liste des modeles

```bash
curl http://localhost:8191/v1/models
```

### Dechargement du modele (admin)

```bash
curl -X POST http://localhost:8191/admin/unload
```

## Parametres supportes

| Parametre | Type | Default | Description |
|-----------|------|---------|-------------|
| `input` | string | (requis) | Texte a synthetiser (max 4096 caracteres) |
| `voice` | string | `alloy` | Voix a utiliser (voir section Voix) |
| `response_format` | string | `mp3` | Format de sortie (voir section Formats) |
| `speed` | float | `1.0` | Vitesse de lecture (0.25 a 4.0) |
| `model` | string | `tts-1` | Modele : `tts-1`, `tts-1-hd`, ou `kokoro` |

## Voix

Noms OpenAI-compatibles mappes aux voix Kokoro internes :

| Nom API | Voix Kokoro | Genre |
|---------|-------------|-------|
| `alloy` | af_sky | F |
| `echo` | am_adam | M |
| `fable` | af_bella | F |
| `onyx` | am_michael | M |
| `nova` | af_nova | F |
| `shimmer` | af_sarah | F |

Les voix Kokoro natives (`af_sky`, `af_bella`, `am_adam`, `am_michael`) sont aussi acceptees directement.

## Formats de sortie

| Format | Media type | Remarque |
|--------|-----------|----------|
| `mp3` | audio/mpeg | Encodage via ffmpeg (128 kbps) |
| `wav` | audio/wav | Direct |
| `flac` | audio/flac | Sans perte |
| `pcm` | audio/pcm | Float32 brut |
| `opus` | audio/wav | Fallback WAV (opus non encode) |
| `aac` | audio/wav | Fallback WAV |

## Configuration (.env)

| Variable | Default | Description |
|----------|---------|-------------|
| `TTS_DEVICE` | `cuda` | Peripherique (`cuda` ou `cpu`) |
| `DEFAULT_TTS_MODEL` | `kokoro` | Modele par defaut |
| `DEFAULT_TTS_VOICE` | `af_sky` | Voix par defaut |
| `SAMPLE_RATE` | `24000` | Taux d'echantillonnage (Hz) |
| `PRELOAD_MODEL` | `true` | Charger le modele au demarrage |
| `IDLE_TIMEOUT` | `300` | Dechargement apres inactivite (secondes) |
| `TTS_API_KEY` | (vide) | Cle Bearer token pour l'authentification |

## Architecture

- **Chargement paresseux** : le modele est charge au premier appel et decharge automatiquement apres la periode d'inactivite (`IDLE_TIMEOUT`). Un checker en arriere-plan tourne toutes les 60 s.
- **Modules partages** : utilise `../shared/` pour `lazy_model.py` (gestion du cycle de vie) et `auth_middleware.py` (authentification Bearer).
- **Fallback CUDA** : si CUDA n'est pas disponible, le modele bascule sur CPU (`TTS_DEVICE=cpu`).

## Fichiers

| Fichier | Role |
|---------|------|
| `app.py` | Application FastAPI principale |
| `Dockerfile` | Image Python 3.11 avec Kokoro, ffmpeg, espeak-ng |
| `docker-compose.yml` | Configuration build local |
| `docker-compose-hybrid.yml` | Configuration image pre-build (ghcr.io) |
| `.gitignore` | Exclusions git |
| `start.sh` | Script de demarrage du conteneur |
| `.env` | Variables d'environnement (non commite) |
