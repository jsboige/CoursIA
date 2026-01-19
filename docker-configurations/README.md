# Docker Configurations - GenAI Ecosystem

Ce repertoire contient les configurations Docker consolidees pour l'ecosysteme GenAI Images, en parfaite coherence avec les scripts `genai-auth`.

## Structure Organisee

```
docker-configurations/
├── README.md                   (ce fichier)
├── services/                   (configurations Docker des services)
│   ├── comfyui-qwen/          (ComfyUI + Qwen Image-Edit) [PORT 8188]
│   │   ├── docker-compose.yml
│   │   ├── README.md
│   │   └── .env.example
│   ├── forge-turbo/           (Stable Diffusion Forge) [PORT 17861]
│   │   ├── docker-compose.yml
│   │   ├── Dockerfile
│   │   └── README.md
│   └── orchestrator/          (service d'orchestration - experimental)
├── profiles/                   (profils de deploiement GPU)
│   └── README.md              (guide qwen-only, forge-only, dual-gpu)
├── shared/                     (ressources partagees entre services)
├── cache/                      (cache HuggingFace, CivitAI)
├── models/                     (modeles partages)
├── .secrets/                   (tokens authentification - gitignore)
├── docs/                       (documentation infrastructure)
├── logs/                       (logs des services)
└── _archive-20251125/         (configurations obsoletes archivees)
```

## Allocation GPU

| GPU | Modele | VRAM | Service | Port |
|-----|--------|------|---------|------|
| 0 (PyTorch) | RTX 3090 | 24 GB | ComfyUI Qwen | 8188 |
| 1 (PyTorch) | RTX 3080 Ti | 16 GB | Forge Turbo | 17861 |

**Note**: Le mapping PyTorch est inverse par rapport a nvidia-smi.

## Services Principaux

### `services/comfyui-qwen/` - ComfyUI + Qwen Image-Edit

Configuration principale pour ComfyUI avec le modele Qwen-Image-Edit-2509-FP8.

**Demarrage** :
```bash
cd docker-configurations/services/comfyui-qwen
cp .env.example .env
docker-compose up -d
```

**Acces** : http://localhost:8188 (authentification Bearer Token)

Voir [services/comfyui-qwen/README.md](services/comfyui-qwen/README.md)

### `services/forge-turbo/` - Stable Diffusion Forge

Service Docker pour Stable Diffusion WebUI Forge optimise SDXL Turbo.

**Demarrage** :
```bash
cd docker-configurations/services/forge-turbo
cp .env.example .env
docker-compose up -d
```

**Acces** : http://localhost:17861 (authentification Gradio Basic)

Voir [services/forge-turbo/README.md](services/forge-turbo/README.md)

## Profils de Deploiement

Voir [profiles/README.md](profiles/README.md) pour les profils disponibles:

| Profil | Services | GPUs |
|--------|----------|------|
| `qwen-only` | ComfyUI Qwen | RTX 3090 |
| `forge-only` | Forge Turbo | RTX 3080 Ti |
| `dual-gpu` | ComfyUI + Forge | Les deux |

## Ressources Partagees

### `models/` - Modeles Partages

Volume partage pour tous les modeles GenAI.

### `cache/` - Cache Partage

Volume partage pour le cache HuggingFace, CivitAI, etc.

## Integration avec Scripts GenAI-Auth

Scripts de gestion dans `../scripts/genai-auth/core/`:

| Script | Description |
|--------|-------------|
| `setup_complete_qwen.py` | Installation complete automatisee |
| `validate_genai_ecosystem.py` | Validation de l'ecosysteme |
| `diagnose_comfyui_auth.py` | Diagnostic authentification |

## Configurations Archivees

Les configurations obsoletes sont dans `_archive-20251125/`:
- Anciens docker-compose.yml multi-services
- Configurations incompletes (flux-1-dev, stable-diffusion-35)

Voir `_archive-20251125/README.md` pour les details.

## Prerequis

- **Docker Desktop** avec support WSL2 et NVIDIA Docker Runtime
- **GPU**: RTX 3090 (24GB) + RTX 3080 Ti (16GB) recommandes
- **RAM**: 32GB+ recommande
- **Stockage**: 100GB+ pour les modeles

## Securite

- **Tokens**: Stockes dans `.secrets/` (gitignore)
- **ComfyUI**: Authentification Bearer Token (hash bcrypt)
- **Forge**: Authentification Gradio Basic

## Documentation

- [Architecture GenAI](../docs/genai/architecture.md)
- [Guide Utilisateur](../docs/genai/user-guide.md)
- [Troubleshooting](../docs/genai/troubleshooting.md)
- [Scripts GenAI-Auth](../scripts/genai-auth/README.md)

## Depannage

```bash
# Logs container
docker-compose logs comfyui-qwen

# GPU disponible
docker exec comfyui-qwen nvidia-smi

# Diagnostic auth
python scripts/genai-auth/core/diagnose_comfyui_auth.py
```

Voir [../docs/genai/troubleshooting.md](../docs/genai/troubleshooting.md) pour plus de details.

---

**Derniere mise a jour**: 2025-01-19
**Version**: 3.0.0 - Structure consolidee Phase 3
**Statut**: Production Ready