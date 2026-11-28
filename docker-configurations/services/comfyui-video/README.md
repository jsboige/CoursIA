# ComfyUI Video - Video Generation

Configuration Docker pour ComfyUI avec support video (HunyuanVideo, Wan 2.1/2.2, AnimateDiff) sur GPU RTX 3090.

## Overview

| Parametre | Valeur |
|-----------|--------|
| Modeles | HunyuanVideo, Wan 2.1/2.2, AnimateDiff |
| Port | 8189 |
| GPU | RTX 3090 (carte nvidia-smi GPU 1, seule carte visible de CUDA) |
| VRAM | ~9GB+ (selon modele charge) |
| URL cloud | https://comfyui-video.myia.io |

## Demarrage

```bash
# Depuis docker-configurations/services/comfyui-video/
docker-compose up -d

# Suivre les logs
docker-compose logs -f

# Arreter
docker-compose down
```

## Custom Nodes

| Node | Repository | Description |
|------|-----------|-------------|
| ComfyUI-AnimateDiff-Evolved | Kosinkadink/ComfyUI-AnimateDiff-Evolved | Animation et generation video |
| ComfyUI-VideoHelperSuite | Kosinkadink/ComfyUI-VideoHelperSuite | Utilitaires video (load, save, combine) |
| ComfyUI-HunyuanVideoWrapper | kijai/ComfyUI-HunyuanVideoWrapper | Tencent HunyuanVideo |
| ComfyUI-GGUF | city96/ComfyUI-GGUF | Support modeles GGUF quantizes |

## Configuration (.env)

Copier `.env.example` vers `.env` et adapter les valeurs :

```bash
cp .env.example .env
```

| Variable | Defaut | Description |
|----------|--------|-------------|
| `GPU_DEVICE_ID` | `0` | Carte visee, par son index nvidia-smi (0 = RTX 3080 Ti, 1 = RTX 3090) ; a regler sur `1` dans le `.env` |
| `CUDA_VISIBLE_DEVICES` | celle de `GPU_DEVICE_ID` | Cartes visibles de CUDA : c'est ce reglage qui isole la carte |
| `COMFYUI_VIDEO_PORT` | `8189` | Port externe |
| `COMFYUI_WORKSPACE_PATH` | `./workspace` | Chemin workspace ComfyUI |
| `CIVITAI_TOKEN` | - | Token CivitAI pour telechargement modeles |
| `HF_TOKEN` | - | Token Hugging Face |
| `COMFYUI_LOGIN_ENABLED` | `true` | Activer authentification |
| `COMFYUI_USERNAME` | - | Utilisateur |
| `COMFYUI_VIDEO_PASSWORD` | - | Mot de passe (centralise `.secrets/master.env` via `render_envs.py`, #10985) |
| `COMFYUI_VIDEO_TOKEN` | - | Bearer token API |
| `API_TIMEOUT` | `600` | Timeout requetes API (secondes) |

### Mapping GPU

Deux reglages se lisent ensemble, tous deux portes par `docker-compose.yml` :

- `CUDA_DEVICE_ORDER=PCI_BUS_ID` : l'index d'une carte sous CUDA est son index `nvidia-smi` (0 = RTX 3080 Ti, 16 GB ; 1 = RTX 3090, 24 GB). Sans cette variable, l'ordre par defaut de CUDA est l'inverse de celui de `nvidia-smi`.
- `CUDA_VISIBLE_DEVICES` : la liste des cartes que CUDA voit dans le conteneur. C'est le seul reglage qui isole : sur le banc po-2023 (WSL2), `device_ids` et `NVIDIA_VISIBLE_DEVICES` laissent les deux cartes visibles (mesure du 2026-11-24).

`GPU_DEVICE_ID=1` vise la RTX 3090. L'entrypoint la passe telle quelle a `--cuda-device`, et c'est bien l'identifiant `nvidia-smi` qu'attend ComfyUI : son `main.py` recopie cette valeur dans `CUDA_VISIBLE_DEVICES`, en **remplacant** le masque du conteneur, avant tout import de `torch`. La traduire en position dans la liste visible (`0` quand la carte est seule) envoie donc le serveur sur l'autre carte — c'est la mesure du 2026-11-28 ci-dessous. Si la carte visee n'est pas dans le masque, le demarrage s'arrete sur un message explicite.

**Controle.** `nvidia-smi -L` liste les cartes quel que soit le masque : ce n'est pas un temoin du reglage. Le temoin qui fait foi est celui du serveur lui-meme, dans ses logs de demarrage — c'est lui qui choisit sa carte :

```bash
docker logs comfyui-video 2>&1 | grep -E 'Carte nvidia-smi|Device: cuda|Total VRAM'
```

Attendu avec `GPU_DEVICE_ID=1` et `CUDA_VISIBLE_DEVICES=1`, sur une 3090 de 24 Go :

```
Carte nvidia-smi 1 (CUDA_VISIBLE_DEVICES=1)
Total VRAM 24576 MB, total RAM ...
Device: cuda:0 NVIDIA GeForce RTX 3090 : ...
```

La ligne `Total VRAM` tranche a elle seule : `16384 MB` = 3080 Ti, `24576 MB` = 3090.

Le controle `torch` dans le conteneur ne mesure que le masque, pas la carte que ComfyUI retient : le 2026-11-28 il rendait `1 ['NVIDIA GeForce RTX 3090']` alors que le serveur venait de demarrer sur la 3080 Ti (`Total VRAM 16384 MB`). Il reste utile pour verifier le masque seul :

```bash
docker exec comfyui-video venv/bin/python3 -c "import torch; n=torch.cuda.device_count(); print(n, [torch.cuda.get_device_name(i) for i in range(n)])"
```

**Cartes distinctes avec `comfyui-qwen`** : ce service vise la RTX 3090 (GPU 1, masque `1` + `PCI_BUS_ID`), `comfyui-qwen` la RTX 3080 Ti (GPU 0, masque `0` + `PCI_BUS_ID`). L'ancienne exclusivite entre les deux est levee (decision #28423 §5) : elle etait de surcroit infeasible, 24-26 Go sur une carte de 24 Go.

## Architecture

- **Base** : ComfyUI compile depuis les sources, Python 3.11, PyTorch CUDA 12.1
- **Quantization** : Support INT8/FP8 via Optimum Quanto + bitsandbytes
- **GGUF** : Support modeles GGUF quantizes via ComfyUI-GGUF
- **Idle Monitor** : Sidecar qui decharge les modeles apres inactivite (`IDLE_TIMEOUT=1200s`)
- **Auth** : ComfyUI-Login avec bcrypt

## Fichiers

| Fichier | Description |
|---------|-------------|
| `docker-compose.yml` | Service principal + sidecar idle-monitor |
| `entrypoint.sh` | Installation auto + lancement ComfyUI |
| `install_video_nodes.sh` | Installation manuelle des custom nodes |
| `.env.example` | Template de configuration |

## Volumes

Le workspace ComfyUI est separe de comfyui-qwen pour eviter les conflits de custom nodes et de configuration :

| Source hote | Cible container | Description |
|-------------|-----------------|-------------|
| `COMFYUI_WORKSPACE_PATH` | `/workspace/ComfyUI` | Code + venv + custom nodes |
| `../../shared/models` | `/workspace/ComfyUI/models` | Modeles partages |
| `../../shared/cache` | `/workspace/ComfyUI/cache` | Cache Hugging Face |
| `../../shared/outputs` | `/workspace/ComfyUI/output` | Sorties generees |
