# Profils de Deploiement GenAI

Ce repertoire definit les profils de deploiement pour la stack GenAI.

## Contrainte Materielle

La machine dispose de deux GPUs avec des contraintes memoire:

| GPU Index | Modele | VRAM | Usage Recommande |
|-----------|--------|------|------------------|
| 0 | RTX 3080 Ti Laptop | 16 GB | Forge SD XL Turbo |
| 1 | RTX 3090 | 24 GB | ComfyUI Qwen/Z-Image |

**ATTENTION**: Le mapping PyTorch est inverse par rapport a nvidia-smi:
- `CUDA_VISIBLE_DEVICES=0` dans ComfyUI utilise la RTX 3090 (nvidia-smi GPU 1)
- `--gpu-device-id 1` dans Forge utilise la RTX 3080 Ti (nvidia-smi GPU 0)

## Profils Disponibles

### 1. `qwen-only` - ComfyUI Qwen Image-Edit

**Services**: comfyui-qwen
**GPU**: RTX 3090 (24GB)
**Port**: 8188
**VRAM Estimee**: 12-18GB

```powershell
# Demarrage
docker compose -f docker-configurations/services/comfyui-qwen/docker-compose.yml up -d

# Arret
docker compose -f docker-configurations/services/comfyui-qwen/docker-compose.yml down
```

**Cas d'usage**: Generation/edition d'images avec modele Qwen-Image-Edit-2509-FP8.

---

### 2. `forge-only` - Stable Diffusion Forge Turbo

**Services**: forge-turbo
**GPU**: RTX 3080 Ti (16GB)
**Port**: 17861
**VRAM Estimee**: 8-14GB

```powershell
# Demarrage
docker compose -f docker-configurations/services/forge-turbo/docker-compose.yml up -d

# Arret
docker compose -f docker-configurations/services/forge-turbo/docker-compose.yml down
```

**Cas d'usage**: Generation rapide SDXL Turbo, tests iteratifs.

---

### 3. `dual-gpu` - ComfyUI + Forge en parallele

**Services**: comfyui-qwen + forge-turbo
**GPU**: RTX 3090 (Qwen) + RTX 3080 Ti (Forge)
**Ports**: 8188 + 17861
**VRAM Totale**: ~30GB (reparti sur 2 GPUs)

```powershell
# Demarrage (via script unifie)
.\scripts\genai-stack\manage-genai-stack.ps1 -Action start

# Ou manuellement
docker compose -f docker-configurations/services/comfyui-qwen/docker-compose.yml up -d
docker compose -f docker-configurations/services/forge-turbo/docker-compose.yml up -d

# Arret
.\scripts\genai-stack\manage-genai-stack.ps1 -Action stop
```

**Cas d'usage**: Travail simultane sur deux pipelines differents.

---

### 4. `full-genai` - Stack Complete avec Orchestrateur

**Services**: orchestrator + comfyui-qwen + forge-turbo
**GPU**: Les deux GPUs
**Ports**: 8090 (API), 8188 (ComfyUI), 17861 (Forge)

```powershell
# Demarrage orchestrateur (optionnel, gere les autres services)
docker compose -f docker-configurations/services/orchestrator/docker-compose.yml up -d
```

**Note**: L'orchestrateur dans `services/orchestrator/` contient des services non implementes (flux-1-dev, sd35, comfyui-workflows). A nettoyer.

---

## Estimation VRAM par Modele

| Modele | VRAM Min | VRAM Recommandee | GPU Cible |
|--------|----------|------------------|-----------|
| Qwen-Image-Edit-2509-FP8 | 12 GB | 18 GB | RTX 3090 |
| Z-Image Turbo (Lumina-Next) | 6 GB | 8 GB | RTX 3090 |
| SDXL Turbo | 6 GB | 10 GB | RTX 3080 Ti |
| SD 1.5 | 4 GB | 6 GB | RTX 3080 Ti |

## Verification VRAM

```powershell
# Script de verification
python scripts/genai-stack/check_vram.py

# Ou directement
nvidia-smi --query-gpu=index,name,memory.used,memory.free --format=csv
```

## Bonnes Pratiques

1. **Ne jamais lancer tous les services simultanement** sur un seul GPU
2. **Verifier la VRAM disponible** avant de lancer un profil
3. **Utiliser le script manage-genai-stack.ps1** pour gerer le profil dual-gpu
4. **Monitorer avec nvidia-smi** pendant l'utilisation intensive

## Commandes Utiles

```powershell
# Status complet
.\scripts\genai-stack\manage-genai-stack.ps1 -Action status

# Validation stack ComfyUI
python scripts/genai-stack/validate_stack.py --auth-only

# Logs conteneurs
docker logs comfyui-qwen --tail 50
docker logs forge-turbo --tail 50
```

---

**Derniere mise a jour**: 2025-01-19
**Version**: 1.0.0
