# Demucs API - Music Source Separation

API HTTP pour la separation de sources audio (extraction de stems) avec Demucs v4.

| Parametre | Valeur |
|-----------|--------|
| Modele | htdemucs_ft (Hybrid Transformer, fine-tune) |
| Port | 8193 |
| GPU | GPU 1, RTX 3090 (24 Go) |
| VRAM | ~4 Go |
| Idle timeout | 300s (auto-unload) |
| URL cloud | https://demucs-api.myia.io |

## Demarrage

```bash
# Image pre-construite (production, GPU 1)
docker compose -f docker-compose.yml up -d

# Build local (developpement, GPU 0)
docker compose -f docker-compose-hybrid.yml up -d --build

# Logs
docker compose logs -f demucs-api
```

## Endpoints API

### Health check

```bash
curl https://demucs-api.myia.io/health
```

```json
{
  "status": "healthy",
  "model": "htdemucs_ft",
  "device": "cuda",
  "cuda_available": true,
  "model_loaded": false,
  "idle_timeout": 300
}
```

### Separation de sources

```bash
# Separation complete (ZIP avec 4 stems)
curl -X POST https://demucs-api.myia.io/v1/separate \
  -H "Authorization: Bearer $DEMUCS_API_KEY" \
  -F "file=@song.mp3" \
  -F "model=htdemucs_ft" \
  -o stems.zip

# Extraction vocales uniquement
curl -X POST https://demucs-api.myia.io/v1/separate/vocals \
  -H "Authorization: Bearer $DEMUCS_API_KEY" \
  -F "file=@song.mp3" \
  -o vocals.wav

# Extraction instrumentale
curl -X POST https://demucs-api.myia.io/v1/separate/instrumental \
  -H "Authorization: Bearer $DEMUCS_API_KEY" \
  -F "file=@song.mp3" \
  -o instrumental.zip
```

### Modeles disponibles

```bash
curl https://demucs-api.myia.io/v1/models
```

### Dechargement manuel (admin)

```bash
curl -X POST https://demucs-api.myia.io/admin/unload \
  -H "Authorization: Bearer $DEMUCS_API_KEY"
```

## Parametres supportes

| Parametre | Type | Defaut | Description |
|-----------|------|--------|-------------|
| `file` | fichier | (requis) | Fichier audio a separer (mp3, wav, flac, ogg) |
| `model` | string | htdemucs_ft | Modele Demucs a utiliser |
| `output_format` | string | wav | Format de sortie (wav, mp3, flac) |
| `stems` | string | (tous) | Stems a extraire, separes par virgule |
| `return_zip` | bool | true | Retourner un ZIP (true) ou un fichier unique (false) |

## Variantes de modeles

| Modele | Qualite | VRAM | Description |
|--------|---------|------|-------------|
| `htdemucs_ft` | Excellente | ~4 Go | Hybrid Transformer fine-tune (defaut, recommande) |
| `htdemucs` | Meilleure | ~4 Go | Hybrid Transformer standard |
| `mdx` | Bonne | ~2 Go | MDX Network, plus rapide |
| `mdx_extra` | Bonne | ~3 Go | MDX avec poids supplementaires |

## Sortie

La separation retourne un fichier ZIP contenant les stems extraits :

- `vocals.wav` -- Voix et chant
- `drums.wav` -- Percussions et batterie
- `bass.wav` -- Instruments basses
- `other.wav` -- Autres instruments

## Configuration (.env)

| Variable | Defaut | Description |
|----------|--------|-------------|
| `DEMUCS_MODEL` | htdemucs_ft | Modele par defaut |
| `DEMUCS_DEVICE` | cuda | Peripherique (cuda / cpu) |
| `IDLE_TIMEOUT` | 300 | Secondes avant auto-unload du modele |
| `DEMUCS_SEGMENTS` | (auto) | Segments pour le traitement long |
| `DEMUCS_API_KEY` | (requis) | Cle API bearer token |

## Architecture

- **Chargement paresseux** : le modele est charge en GPU uniquement a la premiere requete, puis decharge automatiquement apres `IDLE_TIMEOUT` secondes d'inactivite (module `../shared/lazy_model.py`)
- **Modules partages** : `../shared/` fournit `lazy_model.py` (gestion du cycle de vie GPU) et `auth_middleware.py` (authentification Bearer token)
- **Fallback CUDA** : detection automatique CUDA, fallback CPU si GPU indisponible
- **Conversion audio** : FFmpeg pour la gestion des formats d'entree ; torchaudio pour le resampling automatique vers la frequence du modele (44100 Hz)

## Fichiers

| Fichier | Description |
|---------|-------------|
| `app.py` | Application FastAPI principale |
| `Dockerfile` | Image Docker (Python 3.11, Demucs v4) |
| `docker-compose.yml` | Configuration production (image ghcr.io, GPU 1) |
| `docker-compose-hybrid.yml` | Configuration developpement (build local, GPU 0) |
| `start.sh` | Script de demarrage uvicorn |
| `.env` | Variables d'environnement locales |
