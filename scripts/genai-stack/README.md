# GenAI Stack - CLI Unifie

CLI Python pour la gestion de l'infrastructure GenAI (ComfyUI + Forge + vLLM Z-Image).

## Quick Start

```bash
# Installation des dependances
pip install -r scripts/genai-stack/requirements.txt

# Aide globale
python scripts/genai-stack/genai.py --help

# Statut des services Docker
python scripts/genai-stack/genai.py docker status

# Validation complete
python scripts/genai-stack/genai.py validate --full

# Verification GPU
python scripts/genai-stack/genai.py gpu
```

## Commandes

### docker - Gestion des services Docker

```bash
genai.py docker status [--remote]          # Statut de tous les services
genai.py docker start <service|all> [--build]  # Demarrer un service
genai.py docker stop <service|all>         # Arreter un service
genai.py docker restart <service|all>      # Redemarrer un service
genai.py docker logs <service> [--tail N]  # Afficher les logs
genai.py docker test [--remote]            # Tester les endpoints
```

Services disponibles : `comfyui-qwen`, `forge-turbo`, `vllm-zimage`, `all`

### validate - Validation stack ComfyUI + services

```bash
genai.py validate --full                   # Validation complete (auth + nodes + generation)
genai.py validate --auth-only              # Authentification uniquement
genai.py validate --nodes-only             # Custom nodes uniquement
genai.py validate --nunchaku               # Test Nunchaku INT4 Lightning (4GB VRAM)
genai.py validate --notebooks              # Validation syntaxe notebooks GenAI
genai.py validate --notebooks --group qwen # Validation d'un groupe specifique
genai.py validate --check-forge            # Verifier aussi Forge-Turbo
genai.py validate --check-vllm             # Verifier aussi vLLM Z-Image
```

### notebooks - Validation par Papermill

```bash
genai.py notebooks                         # Valider tous les notebooks GenAI
genai.py notebooks <target>                # Valider un dossier ou fichier
genai.py notebooks --cleanup               # Nettoyer apres validation
```

### models - Gestion des modeles

```bash
genai.py models download-qwen [--dest DIR] [--docker]  # Modeles Qwen FP8 (~29GB)
genai.py models download-nunchaku [--model NAME]        # Modeles Nunchaku INT4 (~4GB)
genai.py models download-nunchaku --list                # Lister variantes Nunchaku
genai.py models setup-zimage                            # Configurer Z-Image/Lumina
genai.py models list-checkpoints                        # Lister checkpoints ComfyUI
genai.py models list-nodes                              # Lister custom nodes ComfyUI
```

### gpu - Verification GPU

```bash
genai.py gpu                               # Verification VRAM (nvidia-smi)
genai.py gpu --detailed                    # Docker + PyTorch validation
genai.py gpu --json                        # Sortie JSON
```

### auth - Gestion authentification

```bash
genai.py auth init                         # Initialiser les tokens
genai.py auth sync                         # Synchroniser tokens
genai.py auth audit                        # Audit securite
genai.py auth get-token                    # Afficher le token actuel
genai.py auth reconstruct-env              # Reconstruire .env
```

## Architecture des services

| Service | Port | GPU | VRAM | URL Remote |
|---------|------|-----|------|-----------|
| **comfyui-qwen** | 8188 | 0 | 20GB+ | qwen-image-edit.myia.io |
| **forge-turbo** | 17861 | 1 | 8GB+ | turbo.stable-diffusion-webui-forge.myia.io |
| **vllm-zimage** | 8001 | 1 | 15GB+ | z-image.myia.io |

### Authentification

- **ComfyUI** : Bearer Token (hash bcrypt), gere par `genai.py auth`
- **Forge-Turbo** : Basic Auth (variables `FORGE_USER` / `FORGE_PASSWORD` dans `.env`)
- **vLLM Z-Image** : Pas d'authentification

## Structure

```
scripts/genai-stack/
|-- genai.py                    # CLI unifie (point d'entree principal)
|-- config.py                   # Configuration partagee (services, chemins, constantes)
|-- requirements.txt            # Dependances Python
|-- README.md
|-- NUNCHAKU_INSTALLATION.md
|
|-- core/                       # Bibliotheque noyau
|   |-- auth_manager.py         # Gestion authentification centralisee
|   |-- comfyui_client.py       # Client API ComfyUI
|
|-- commands/                   # Sous-commandes du CLI
|   |-- docker.py               # Gestion services Docker
|   |-- validate.py             # Validation ComfyUI + services
|   |-- notebooks.py            # Validation notebooks Papermill
|   |-- models.py               # Telechargement et gestion modeles
|   |-- gpu.py                  # Verification GPU/VRAM
|   |-- auth.py                 # Facade authentification
|
|-- config/models_config.json   # Configuration modeles
|-- workflows/                  # Workflows de test ComfyUI (6 JSON)
|
|-- archive/                    # Scripts legacy archives (voir ARCHIVE_README.md)
|
|-- Wrappers retrocompatibilite (appellent commands/) :
|   docker_manager.py, validate_stack.py, validate_notebooks.py,
|   check_vram.py, list_models.py, list_nodes.py, download_qwen_models.py,
|   download_nunchaku_model.py, setup_z_image.py, test_nunchaku_generation.py
```

## Installation

```bash
pip install -r scripts/genai-stack/requirements.txt
```

Dependances : `requests`, `bcrypt`, `python-dotenv`, `huggingface_hub`, `papermill`

## Workflows de test ComfyUI

| Workflow | Description | VRAM | Temps |
|----------|-------------|------|-------|
| `workflow_qwen_native_t2i.json` | Qwen Phase 29 natif | ~29GB | ~60s |
| `workflow_qwen_nunchaku_t2i.json` | Nunchaku INT4 Lightning | ~4GB | ~4s warm |
| `workflow_z_image_reboot.json` | Z-Image/Lumina | ~10GB | ~20s |
| `workflow_test_simple.json` | Test minimal | <1GB | <5s |
| `workflow_benchmark.json` | Benchmark performance | Variable | Variable |

## Variables d'environnement

Fichier : `MyIA.AI.Notebooks/GenAI/.env`

| Variable | Description |
|----------|-------------|
| `COMFYUI_BEARER_TOKEN` | Hash bcrypt pour auth ComfyUI |
| `COMFYUI_RAW_TOKEN` | Token brut (pour login UI) |
| `HF_TOKEN` | Token HuggingFace (telechargement modeles) |
| `FORGE_USER` / `FORGE_PASSWORD` | Auth Forge-Turbo |
| `LOCAL_MODE` | `true` pour Docker local, `false` pour myia.io |

---

**Version** : 3.0.0 (Consolidation CLI - Fevrier 2026)
