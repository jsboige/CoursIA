# Forge Turbo - Stable Diffusion WebUI Forge

Service Docker pour Stable Diffusion WebUI Forge optimise pour SDXL Turbo.

## Configuration Materielle

| Parametre | Valeur |
|-----------|--------|
| GPU Cible | RTX 3080 Ti Laptop (16 GB) |
| GPU Device ID | 1 (nvidia-smi) |
| Port | 17861 (externe) -> 17860 (interne) |
| Image Base | ghcr.io/ai-dock/stable-diffusion-webui-forge:latest-cuda |

## Fichiers

```
forge-turbo/
├── docker-compose.yml    # Configuration Docker Compose
├── Dockerfile            # Image custom avec fix numpy
├── .env                  # Variables d'environnement
├── .env.example          # Template configuration
└── scripts/
    └── supervisor-forge.sh   # Script de demarrage interne
```

## Configuration

### Variables d'Environnement (.env)

```bash
# Port d'acces externe
FORGE_PORT=17861

# Authentification Gradio (Basic Auth)
FORGE_USER=admin
FORGE_PASSWORD=changeme  # A MODIFIER EN PRODUCTION
```

### Arguments CLI

Les arguments sont passes via `CLI_ARGS` dans docker-compose.yml:

```yaml
CLI_ARGS=--ui-settings-file config-turbo.json \
         --api \
         --api-log \
         --listen \
         --gradio-auth ${FORGE_USER}:${FORGE_PASSWORD} \
         --gpu-device-id 1 \
         --cuda-malloc \
         --xformers
```

| Argument | Description |
|----------|-------------|
| `--api` | Active l'API REST |
| `--api-log` | Log des appels API |
| `--listen` | Ecoute sur 0.0.0.0 |
| `--gradio-auth` | Authentification Basic |
| `--gpu-device-id 1` | Utilise la RTX 3080 Ti |
| `--cuda-malloc` | Optimisation memoire CUDA |
| `--xformers` | Acceleration attention |

## Demarrage

```powershell
# Depuis la racine du projet
docker compose -f docker-configurations/services/forge-turbo/docker-compose.yml up -d

# Ou via le script de gestion
.\scripts\genai-stack\manage-genai-stack.ps1 -Action start
```

## Acces

- **URL**: http://localhost:17861
- **Auth**: admin / changeme (modifier dans .env)
- **API**: http://localhost:17861/sdapi/v1/

## Dockerfile Custom

Le Dockerfile corrige un probleme de compatibilite numpy dans l'image de base:

```dockerfile
# Fix numpy binary incompatibility
RUN pip uninstall -y numpy opencv-python opencv-python-headless scikit-image Pillow && \
    pip install "numpy<2" opencv-python-headless scikit-image Pillow
```

**Probleme resolu**: Incompatibilite binaire entre numpy 2.x et les bibliotheques pre-compilees (opencv, scikit-image).

## Volumes

| Volume Host | Volume Container | Description |
|-------------|------------------|-------------|
| `../../shared/models` | `/opt/storage/stable_diffusion/models` | Modeles partages |
| `../../shared/outputs` | `/opt/storage/stable_diffusion/outputs` | Images generees |

## Monitoring

```powershell
# Logs
docker logs forge-turbo --tail 100 -f

# Statut
docker ps --filter "name=forge-turbo"

# Utilisation GPU
nvidia-smi
```

## API Endpoints

| Endpoint | Methode | Description |
|----------|---------|-------------|
| `/sdapi/v1/txt2img` | POST | Generation texte vers image |
| `/sdapi/v1/img2img` | POST | Image vers image |
| `/sdapi/v1/sd-models` | GET | Liste des modeles |
| `/sdapi/v1/options` | GET/POST | Configuration |
| `/internal/ping` | GET | Health check |

### Exemple API

```python
import requests

url = "http://localhost:17861/sdapi/v1/txt2img"
payload = {
    "prompt": "a photo of a cat",
    "steps": 4,  # SDXL Turbo = 4 steps
    "width": 1024,
    "height": 1024,
    "cfg_scale": 1.0  # Turbo = cfg 1
}

response = requests.post(url, json=payload, auth=("admin", "changeme"))
```

## Troubleshooting

### Le conteneur ne demarre pas

1. Verifier les logs:
```powershell
docker logs forge-turbo
```

2. Verifier que le GPU est disponible:
```powershell
docker run --rm --gpus all nvidia/cuda:12.4.0-base-ubuntu22.04 nvidia-smi
```

### Erreur numpy/opencv

Le Dockerfile devrait corriger ce probleme. Si l'erreur persiste:
```powershell
# Rebuild l'image
docker compose -f docker-configurations/services/forge-turbo/docker-compose.yml build --no-cache
```

### Port deja utilise

```powershell
# Verifier qui utilise le port
netstat -ano | findstr "17861"

# Modifier le port dans .env
FORGE_PORT=17862
```

### GPU non detectee

Verifier le mapping GPU:
```powershell
# nvidia-smi GPU 0 = RTX 3080 Ti (device_id 1 pour Forge)
# nvidia-smi GPU 1 = RTX 3090 (device_id 0 pour ComfyUI)
nvidia-smi
```

## Performance

| Modele | Steps | Resolution | Temps |
|--------|-------|------------|-------|
| SDXL Turbo | 4 | 1024x1024 | ~2s |
| SDXL Base | 20 | 1024x1024 | ~15s |
| SD 1.5 | 20 | 512x512 | ~5s |

## Integration avec ComfyUI

Forge et ComfyUI peuvent tourner simultanement sur des GPUs differents:

```
RTX 3080 Ti (GPU 0) -> Forge (port 17861)
RTX 3090 (GPU 1)    -> ComfyUI (port 8188)
```

Utiliser le script de gestion pour orchestrer les deux:
```powershell
.\scripts\genai-stack\manage-genai-stack.ps1 -Action start
```

---

**Derniere mise a jour**: 2025-01-19
**Version**: 1.0.0
**Image**: forge-turbo:custom-numpy-fix
