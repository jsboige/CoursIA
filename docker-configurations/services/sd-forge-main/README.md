# SD Forge Main - Stable Diffusion WebUI Forge

Service Docker pour Stable Diffusion WebUI Forge avec support SDXL 1.0 complet.

## Vue d'ensemble

| Parametre | Valeur |
|-----------|--------|
| Modele | SDXL 1.0 |
| Port | 7860 |
| GPU | GPU 1 (RTX 3090, 24 GB) |
| VRAM | ~2 GB |
| URL cloud | https://stable-diffusion-webui-forge.myia.io |
| Image base | ghcr.io/ai-dock/stable-diffusion-webui-forge:latest-cuda |

## Demarrage

```powershell
# Depuis la racine du projet
docker compose -f docker-configurations/services/sd-forge-main/docker-compose.yml up -d

# Arret
docker compose -f docker-configurations/services/sd-forge-main/docker-compose.yml down

# Logs
docker logs sd-forge-main --tail 100 -f
```

## Configuration

### Variables d'environnement (.env

| Variable | Description | Defaut |
|----------|-------------|--------|
| `SD_FORGE_MAIN_API_KEY` | Cle API pour l'authentification | A definir |
| `FORGE_USER` (via `WEB_USER`) | Utilisateur Gradio | `admin` |
| `FORGE_PASSWORD` (via `WEB_PASSWORD`) | Mot de passe Gradio | `changeme` |

### Arguments CLI

Les arguments sont passes via `FORGE_ARGS` dans docker-compose.yml :

| Argument | Description |
|----------|-------------|
| `--api` | Active l'API REST |
| `--api-log` | Log des appels API |
| `--listen` | Ecoute sur 0.0.0.0 |
| `--gradio-auth` | Authentification Gradio |
| `--gpu-device-id 1` | Utilise la RTX 3090 (GPU 1) |
| `--xformers` | Optimisation attention (acceleration) |
| `--skip-install` | Saute l'installation au demarrage |

## Fonctionnalites

- **Gradio WebUI** : Interface web complete pour la generation d'images
- **Xformers** : Optimisation de la memoire et acceleration des calculs d'attention
- **SDXL 1.0** : Support complet du modele SDXL (1024x1024 natif)
- **API REST** : Endpoints `/sdapi/v1/` pour integration programmatique
- **Stockage partage** : Modeles et outputs partages avec les autres services SD

## Architecture

```
Image Docker (Dockerfile custom)
  |
  +-- Base: ghcr.io/ai-dock/stable-diffusion-webui-forge:latest-cuda
  +-- Fix: compatibilite numpy < 2 + opencv-python-headless
  |
  +-- Gradio WebUI (port 7860)
  |     |
  |     +-- txt2img / img2img
  |     +-- API REST (/sdapi/v1/)
  |     +-- Gestion des modeles
  |
  +-- Volumes partages
        |
        +-- ../../shared/models  -> /opt/storage/stable_diffusion/models
        +-- ../../shared/outputs -> /opt/storage/stable_diffusion/outputs
```

## Fichiers

```
sd-forge-main/
  docker-compose.yml   # Configuration Docker Compose
  Dockerfile           # Image custom avec fix numpy/opencv
  .env.example         # Template des variables d'environnement
```

Note : pas de `.gitignore` dedie. Le fichier `.env` est exclu via le `.gitignore` global.

## Volumes

| Volume Host | Volume Container | Description |
|-------------|------------------|-------------|
| `../../shared/models` | `/opt/storage/stable_diffusion/models` | Modeles partages (SDXL, LoRA, VAE) |
| `../../shared/outputs` | `/opt/storage/stable_diffusion/outputs` | Images generees |

## Acces

- **WebUI** : http://localhost:7860
- **Cloud** : https://stable-diffusion-webui-forge.myia.io
- **API** : http://localhost:7860/sdapi/v1/
- **Auth** : admin / changeme (modifier dans `.env`)

## Dockerfile Custom

Le Dockerfile corrige une incompatibilite binaire entre numpy 2.x et les bibliotheques pre-compilees :

```dockerfile
# Fix numpy binary incompatibility
RUN pip uninstall -y numpy opencv-python opencv-python-headless scikit-image Pillow && \
    pip install "numpy<2" opencv-python-headless scikit-image Pillow
```

---

**Derniere mise a jour** : 2026-04-26
**Image** : sd-forge-main:latest
