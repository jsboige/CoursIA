# MusicGen API - Generation de musique par texte

Service HTTP pour la generation de musique a partir de descriptions textuelles, base sur Meta MusicGen (transformers).

| Parametre | Valeur |
|-----------|--------|
| Modele | `facebook/musicgen-medium` (1.5B params) |
| Port | 8192 |
| GPU | GPU 1, RTX 3090 (24 GB) |
| VRAM | ~10 GB (medium) |
| Idle timeout | 300 s (default), 1200 s (docker-compose) |
| URL cloud | `https://musicgen-api.myia.io` |
| Taux echantillonnage | 32000 Hz |

## Demarrage

```bash
# Build et demarrage (local)
docker compose up -d --build

# Demarrage avec image pre-construite (hybride)
docker compose -f docker-compose-hybrid.yml up -d

# Arret
docker compose down

# Logs
docker compose logs -f musicgen-api
```

## Endpoints API

### Health check

```bash
curl http://localhost:8192/health
```

Retourne l'etat du service, la disponibilite CUDA, la memoire GPU et le statut du modele (charge/non charge).

### Generer de la musique

```bash
curl -X POST http://localhost:8192/v1/generate \
  -H "Authorization: Bearer $MUSICGEN_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "prompt": "80s synthwave with heavy bass and arpeggiated synths",
    "duration": 10,
    "temperature": 1.0,
    "top_k": 250,
    "top_p": 0.0,
    "cfg_coef": 3.0,
    "seed": 42,
    "format": "wav"
  }' \
  --output generated.wav
```

Retourne un fichier audio (`audio/wav` ou `audio/mpeg`). Headers de reponse : `X-Duration`, `X-Generation-Time`, `X-Sample-Rate`.

### Modeles disponibles

```bash
curl http://localhost:8192/v1/models
```

### Dechargement manuel (admin)

```bash
curl -X POST http://localhost:8192/admin/unload \
  -H "Authorization: Bearer $MUSICGEN_API_KEY"
```

Libere la memoire GPU en dechargeant le modele. Le modele sera recharge automatiquement a la prochaine requete.

## Parametres de generation

| Parametre | Type | Default | Plage | Description |
|-----------|------|---------|-------|-------------|
| `prompt` | string | (requis) | - | Description textuelle de la musique |
| `duration` | int | 10 | 1-30 | Duree en secondes |
| `temperature` | float | 1.0 | 0.5-1.5 | Temperature d'echantillonnage |
| `top_k` | int | 250 | 0-1000 | Echantillonnage top-k |
| `top_p` | float | 0.0 | 0.0-1.0 | Echantillonnage top-p (0 = desactive) |
| `cfg_coef` | float | 3.0 | 1.0-10.0 | Coefficient de guidance classifier-free |
| `seed` | int | null | - | Graine aleatoire pour reproductibilite |
| `format` | string | "wav" | wav, mp3 | Format de sortie audio |
| `model` | string | - | - | Surcharge du modele (non implemente) |

## Variantes de modele

| Modele | Params | VRAM | Commentaire |
|--------|--------|------|-------------|
| `facebook/musicgen-small` | 300M | ~4 GB | Rapide, qualite correcte |
| `facebook/musicgen-medium` | 1.5B | ~10 GB | Bon compromis qualite/perf |
| `facebook/musicgen-large` | 3.3B | ~20 GB | Meilleure qualite, lent |
| `facebook/musicgen-melody` | 1.5B | ~10 GB | Conditionnement melody |

Le modele se configure via `MUSICGEN_MODEL` dans `.env`.

## Configuration (.env)

| Variable | Default | Description |
|----------|---------|-------------|
| `MUSICGEN_MODEL` | `facebook/musicgen-medium` | Modele HuggingFace a charger |
| `MUSICGEN_DEVICE` | `cuda` | Peripherique (cuda / cpu) |
| `MAX_DURATION` | `30` | Duree maximale en secondes |
| `DEFAULT_DURATION` | `10` | Duree par defaut si non specifiee |
| `PRELOAD_MODEL` | `false` | Charger le modele au demarrage |
| `IDLE_TIMEOUT` | `300` / `1200` | Secondes d'inactivite avant decharge |
| `MUSICGEN_API_KEY` | - | Cle Bearer token pour l'authentification |
| `GPU_DEVICE_ID` | `1` | ID du GPU NVIDIA a utiliser |
| `MODELS_PATH` | `./models` | Chemin des modeles en cache |
| `OUTPUT_PATH` | `./outputs` | Chemin des fichiers de sortie |

## Architecture

- **Chargement paresseux** : le modele n'est charge en GPU qu'a la premiere requete. Apres `IDLE_TIMEOUT` secondes sans requete, le modele est decharge automatiquement pour liberer la VRAM. Module partage : `shared/lazy_model.py`.
- **Modules partages** : `../shared/` est monte en lecture seule et fournit `LazyModelManager`, `idle_checker_task`, et `setup_auth` (authentification Bearer token).
- **Fallback CUDA** : si CUDA n'est pas disponible, le service fonctionne sur CPU (tres lent). Verifier `/health` pour le statut GPU.
- **Traitement asynchrone** : endpoint `/v1/generate/async` avec suivi via `/v1/jobs/{job_id}` pour les generations longues.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `app.py` | Application FastAPI principale |
| `Dockerfile` | Image Python 3.11-slim + torch + transformers |
| `docker-compose.yml` | Configuration Docker (build local) |
| `docker-compose-hybrid.yml` | Configuration Docker (image pre-construite ghcr.io) |
| `.env` | Variables d'environnement du service |
| `start.sh` | Script de demarrage uvicorn |
