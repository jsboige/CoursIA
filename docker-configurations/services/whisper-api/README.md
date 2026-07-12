# Whisper API - Speech-to-Text

Service de transcription audio utilisant faster-whisper avec une API compatible OpenAI.

| Parametre | Valeur |
|-----------|--------|
| Modele | faster-whisper large-v3-turbo |
| Port | 8190 |
| GPU | GPU 1, RTX 3090 |
| VRAM | ~10 GB |
| API | OpenAI `/v1/audio/transcriptions` compatible |
| Timeout inactivite | 300 s |
| URL cloud | `https://whisper-api.myia.io` |

## Demarrage

```bash
# Construction et lancement
docker-compose up -d --build

# Configuration hybride (image pre-construite, GPU 1)
docker-compose -f docker-compose-hybrid.yml up -d

# Verifier le statut
docker-compose ps
docker-compose logs -f whisper-api
```

## Endpoints API

### Health check

```bash
curl http://localhost:8190/health
```

### Transcription

```bash
curl -X POST http://localhost:8190/v1/audio/transcriptions \
  -H "Authorization: Bearer $WHISPER_API_KEY" \
  -F file="@audio.mp3" \
  -F model="whisper-1" \
  -F response_format="json" \
  -F timestamp_granularities[]="segment" \
  -F language="fr"
```

Parametres supportes :

| Parametre | Type | Defaut | Description |
|-----------|------|--------|-------------|
| `file` | file | (requis) | Fichier audio (mp3, mp4, mpeg, mpga, m4a, wav, webm) |
| `model` | string | `whisper-1` | Identifiant du modele (compatibilite OpenAI) |
| `language` | string | auto | Code langue ISO 639-1 (fr, en, de, es...) |
| `response_format` | string | `json` | Format de reponse (json, text, srt, verbose_json, vtt) |
| `timestamp_granularities` | list | `["segment"]` | Granularite des timestamps (`segment` ou `word`) |
| `temperature` | float | `0.0` | Temperature d'echantillonnage (0.0 - 1.0) |

Formats de reponse :

| Format | Description |
|--------|-------------|
| `json` | Texte de la transcription |
| `text` | Texte brut (plain text) |
| `srt` | Sous-titres SRT avec timestamps |
| `verbose_json` | JSON detaille avec segments et metadonnees |
| `vtt` | Sous-titres WebVTT |

### Liste des modeles

```bash
curl http://localhost:8190/v1/models
```

### Dechargement du modele (admin)

```bash
curl -X POST http://localhost:8190/admin/unload \
  -H "Authorization: Bearer $WHISPER_API_KEY"
```

Libere la memoire GPU. Le modele sera recharge a la prochaine requete.

## Configuration

Variables d'environnement (fichier `.env`) :

| Variable | Defaut | Description |
|----------|--------|-------------|
| `WHISPER_MODEL` | `large-v3-turbo` | Taille du modele faster-whisper |
| `WHISPER_DEVICE` | `cuda` | Peripherique de calcul (cuda ou cpu) |
| `WHISPER_COMPUTE_TYPE` | `float16` | Type de calcul (float16, int8) |
| `MAX_FILE_SIZE` | `26214400` | Taille max des fichiers (25 MB) |
| `PRELOAD_MODEL` | `true` | Charger le modele au demarrage |
| `IDLE_TIMEOUT` | `300` | Timeout de dechargement automatique (secondes) |
| `WHISPER_API_KEY` | (vide) | Cle API Bearer token |

## Architecture

- **Chargement paresseux** : Le modele est charge en memoire GPU lors de la premiere requete et decharge apres `IDLE_TIMEOUT` secondes d'inactivite via le module `LazyModelManager` (voir `../shared/lazy_model.py`).
- **Modules partages** : Utilise `../shared/` pour `lazy_model.py` (gestion du cycle de vie modele) et `auth_middleware.py` (authentification Bearer token).
- **Conversion FFmpeg** : Les fichiers audio sont convertis via faster-whisper qui utilise FFmpeg en interne. Les formats supportes sont mp3, mp4, mpeg, mpga, m4a, wav et webm.
- **Fallback CUDA** : Si CUDA n'est pas disponible (ctranslate2 non detecte ou erreur cublas), le service bascule automatiquement sur CPU avec le type de calcul `int8`.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `app.py` | Application FastAPI principale |
| `Dockerfile` | Image Docker basee sur nvidia/cuda:12.1.0 |
| `docker-compose.yml` | Configuration standard (GPU 0, build local) |
| `docker-compose-hybrid.yml` | Configuration hybride (GPU 1, image ghcr.io pre-construite) |
| `start.sh` | Script de demarrage uvicorn |
| `.env` | Variables d'environnement (non commite) |
| `models/` | Cache des modeles faster-whisper |
