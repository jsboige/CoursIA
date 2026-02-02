# GenAI Stack - Scripts de Gestion

Scripts Python et PowerShell pour la gestion de l'infrastructure GenAI (ComfyUI + Forge).

## Points d'Entree Principaux

| Action | Script | Description |
|--------|--------|-------------|
| **Deploiement** | `manage-genai-stack.ps1 -Action start` | Demarre les services Docker |
| **Validation** | `python validate_stack.py --full` | Valide ComfyUI (auth, nodes, generation) |
| **Validation Notebooks** | `python validate_notebooks.py` | Execute les notebooks via Papermill |
| **Validation Ecosysteme** | `python core/validate_genai_ecosystem.py` | Validation complete (fichiers, APIs, auth) |

## Structure Complete

```
scripts/genai-stack/
|-- POINTS D'ENTREE PRINCIPAUX
|   |-- manage-genai-stack.ps1    # Orchestrateur principal (start/stop/restart/status)
|   |-- validate_stack.py         # Suite validation ComfyUI (auth + nodes + generation)
|   |-- validate_notebooks.py     # Validation notebooks Jupyter via Papermill
|
|-- GESTION DES MODELES
|   |-- download_qwen_models.py   # Telecharge modeles Qwen FP8 (~29GB)
|   |-- download_nunchaku_model.py # Telecharge modeles Nunchaku INT4 (~4GB)
|   |-- setup_z_image.py          # Configure Z-Image/Lumina (~10GB)
|   |-- list_models.py            # Liste checkpoints disponibles
|   |-- list_nodes.py             # Liste custom nodes ComfyUI
|   |-- check_vram.py             # Verification VRAM GPUs
|
|-- TESTS SPECIFIQUES
|   |-- test_nunchaku_generation.py # Wrapper pour validate_stack.py --nunchaku
|
|-- core/                         # Modules principaux
|   |-- auth_manager.py           # Gestion authentification centralisee
|   |-- comfyui_client.py         # Client API ComfyUI unifie
|   |-- deploy_comfyui_auth.py    # Deploiement auth ComfyUI-Login
|   |-- cleanup_comfyui_auth.py   # Nettoyage tokens
|   |-- diagnose_comfyui_auth.py  # Diagnostic authentification
|   |-- validate_genai_ecosystem.py # Validation ecosysteme complet
|   |-- validate_mission_documentation.py
|   |-- test_correction_setup_complete.py
|
|-- utils/                        # Utilitaires
|   |-- docker-setup.ps1          # Setup initial Docker
|   |-- docker-start.ps1          # Demarrage Docker
|   |-- docker-stop.ps1           # Arret Docker
|   |-- benchmark.py              # Benchmarks performance
|   |-- diagnostic_utils.py       # Outils diagnostic
|   |-- diagnostic_model_paths.py # Diagnostic chemins modeles
|   |-- token_manager.py          # Gestion tokens legacy
|   |-- token_synchronizer.py     # Synchronisation tokens
|   |-- workflow_utils.py         # Utilitaires workflows
|   |-- validate_gpu_cuda.py      # Validation GPU/CUDA
|   |-- validate_all_models.py    # Validation tous modeles
|   |-- validate_genai_stack.py   # Validation stack (legacy)
|   |-- validate_tokens_simple.py # Validation tokens simple
|   |-- validate_mission_documentation.py
|   |-- test_forge_connectivity.py # Test connexion Forge
|   |-- test_forge_notebook.py    # Test notebook Forge
|   |-- comfyui_client_helper.py  # Helper client legacy
|   |-- consolidated_tests.py     # Tests consolides
|   |-- reconstruct_env.py        # Reconstruction .env
|   |-- debug_proxy.py            # Proxy debug
|
|-- config/                       # Configuration
|   |-- models_config.json        # Config modeles disponibles
|
|-- workflows/                    # Workflows de test ComfyUI
|   |-- workflow_qwen_native_t2i.json    # Workflow Qwen Phase 29 (defaut)
|   |-- workflow_qwen_nunchaku_t2i.json  # Workflow Nunchaku INT4 Lightning
|   |-- workflow_z_image_reboot.json     # Workflow Z-Image/Lumina
|   |-- workflow_benchmark.json          # Benchmark performance
|   |-- workflow_test_simple.json        # Test minimal
|   |-- workflow_sd15_test_green_apple.json
|
|-- NUNCHAKU_INSTALLATION.md      # Guide installation Nunchaku
```

## Scripts Externes Associes

### docker-configurations/

| Script | Emplacement | Role |
|--------|-------------|------|
| `generate_token.py` | `services/comfyui-qwen/` | Genere token bcrypt pour auth |
| `docker-compose.yml` | `services/comfyui-qwen/` | Definition service ComfyUI |
| `orchestrator.py` | `services/orchestrator/` | Orchestrateur multi-services avec API REST |

### MyIA.AI.Notebooks/GenAI/

| Script | Emplacement | Role |
|--------|-------------|------|
| `validate_auth.py` | `00-GenAI-Environment/` | Validation authentification depuis notebook |
| `comfyui_client.py` | `shared/helpers/` | Client ComfyUI pour notebooks |
| `genai_helpers.py` | `shared/helpers/` | Helpers generiques GenAI |

## Commandes de Deploiement

### Demarrage Complet

```powershell
# 1. Verifier VRAM disponible
python scripts/genai-stack/check_vram.py

# 2. Demarrer la stack (ComfyUI + Forge)
.\scripts\genai-stack\manage-genai-stack.ps1 -Action start

# 3. Valider l'authentification
python scripts/genai-stack/validate_stack.py --auth-only

# 4. Validation complete avec generation
python scripts/genai-stack/validate_stack.py --full
```

### Deploiement Automatise (Python)

```bash
python scripts/genai-stack/core/deploy_comfyui_auth.py
python scripts/genai-stack/core/deploy_comfyui_auth.py --force  # Recree conteneur
```

## Commandes de Validation

### validate_stack.py (Principal)

```bash
# Validation complete (auth + nodes + generation)
python scripts/genai-stack/validate_stack.py --full

# Test authentification uniquement
python scripts/genai-stack/validate_stack.py --auth-only

# Test custom nodes uniquement
python scripts/genai-stack/validate_stack.py --nodes-only

# Test avec workflow specifique
python scripts/genai-stack/validate_stack.py --workflow workflow_z_image_reboot.json

# Test Nunchaku INT4 Lightning (4GB VRAM, 4s/image)
python scripts/genai-stack/validate_stack.py --nunchaku

# Validation notebooks syntaxe
python scripts/genai-stack/validate_stack.py --notebooks

# Validation groupe specifique
python scripts/genai-stack/validate_stack.py --group qwen

# Verifier aussi Forge et vLLM
python scripts/genai-stack/validate_stack.py --full --check-forge --check-vllm
```

### validate_notebooks.py (Papermill)

```bash
# Valider tous les notebooks GenAI
python scripts/genai-stack/validate_notebooks.py

# Valider un notebook specifique
python scripts/genai-stack/validate_notebooks.py "MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-1-OpenAI-DALL-E-3.ipynb"

# Nettoyer apres validation
python scripts/genai-stack/validate_notebooks.py --cleanup
```

### validate_genai_ecosystem.py (Ecosysteme Complet)

```bash
# Validation complete ecosysteme
python scripts/genai-stack/core/validate_genai_ecosystem.py

# Mode verbose
python scripts/genai-stack/core/validate_genai_ecosystem.py --verbose

# Avec corrections automatiques
python scripts/genai-stack/core/validate_genai_ecosystem.py --fix

# Generer rapport JSON
python scripts/genai-stack/core/validate_genai_ecosystem.py --report validation_report.json
```

## Commandes de Telechargement des Modeles

### Modeles Qwen FP8 (Phase 29) - ~29GB VRAM

```bash
# Telecharger vers docker-configurations/shared/models
python scripts/genai-stack/download_qwen_models.py

# Telecharger vers chemin specifique
python scripts/genai-stack/download_qwen_models.py --dest /path/to/models

# Telecharger directement dans conteneur Docker
python scripts/genai-stack/download_qwen_models.py --docker
```

**Modeles telecharges:**
- `qwen_image_edit_2509_fp8_e4m3fn.safetensors` (20GB) - UNET
- `qwen_2.5_vl_7b_fp8_scaled.safetensors` (8.8GB) - Text Encoder
- `qwen_image_vae.safetensors` (243MB) - VAE

### Modeles Nunchaku INT4 (Lightning) - ~4GB VRAM

```bash
# Telecharger modele recommande (lightning-4step-r128)
python scripts/genai-stack/download_nunchaku_model.py

# Lister modeles disponibles
python scripts/genai-stack/download_nunchaku_model.py --list

# Telecharger variante specifique
python scripts/genai-stack/download_nunchaku_model.py --model lightning-8step-r128

# Telecharger vers chemin specifique
python scripts/genai-stack/download_nunchaku_model.py --output-dir /path/to/models
```

**Variantes Nunchaku disponibles:**
- `lightning-4step-r128` (recommande) - 4 steps, haute qualite
- `lightning-4step-r32` - 4 steps, plus rapide
- `lightning-8step-r128` - 8 steps, meilleure qualite
- `standard-r128` - 20 steps, qualite maximale

### Z-Image / Lumina - ~10GB

```bash
python scripts/genai-stack/setup_z_image.py
```

## Diagnostic et Troubleshooting

```bash
# Diagnostic authentification
python scripts/genai-stack/core/diagnose_comfyui_auth.py

# Validation GPU/CUDA
python scripts/genai-stack/utils/validate_gpu_cuda.py

# Verifier VRAM
python scripts/genai-stack/check_vram.py

# Tester connectivite Forge
python scripts/genai-stack/utils/test_forge_connectivity.py

# Audit securite tokens
python scripts/genai-stack/core/auth_manager.py audit

# Synchroniser tokens
python scripts/genai-stack/core/auth_manager.py sync

# Reconstruire .env
python scripts/genai-stack/core/auth_manager.py reconstruct-env
```

## Workflows ComfyUI de Test

| Workflow | Description | VRAM | Temps |
|----------|-------------|------|-------|
| `workflow_qwen_native_t2i.json` | Qwen Phase 29 natif | ~29GB | ~60s |
| `workflow_qwen_nunchaku_t2i.json` | Nunchaku INT4 Lightning | ~4GB | ~4s warm |
| `workflow_z_image_reboot.json` | Z-Image/Lumina | ~10GB | ~20s |
| `workflow_test_simple.json` | Test minimal | <1GB | <5s |
| `workflow_benchmark.json` | Benchmark performance | Variable | Variable |

## Integration Docker

Les scripts interagissent avec les conteneurs definis dans:
- `docker-configurations/services/comfyui-qwen/docker-compose.yml`
- `docker-configurations/services/forge-turbo/docker-compose.yml`

### Architecture Docker

```
comfyui-qwen (GPU 0 - RTX 3090)
|-- Port: 8188
|-- Auth: Bearer Token (bcrypt)
|-- Modeles: Qwen FP8/Nunchaku INT4/Z-Image

forge-turbo (GPU 1 - RTX 3080 Ti)
|-- Port: 17861
|-- Auth: Basic Auth
|-- Modeles: SDXL Turbo
```

## Dependances Python

```
requests>=2.28.0
websocket-client>=1.4.0
bcrypt>=4.0.0
python-dotenv>=1.0.0
papermill>=2.4.0
huggingface_hub>=0.20.0
```

Installation:
```bash
pip install requests websocket-client bcrypt python-dotenv papermill huggingface_hub
```

## Variables d'Environnement

Variables requises dans `.secrets/comfyui_auth_tokens.conf` ou `.env`:

| Variable | Description |
|----------|-------------|
| `COMFYUI_BEARER_TOKEN` | Hash bcrypt pour auth ComfyUI |
| `COMFYUI_RAW_TOKEN` | Token brut (pour login UI) |
| `HF_TOKEN` | Token HuggingFace (telechargement modeles) |
| `CIVITAI_TOKEN` | Token CivitAI (optionnel) |
| `GPU_DEVICE_ID` | ID GPU pour ComfyUI (defaut: 0) |

## Exemples d'Usage Complets

### Workflow de Developpement

```powershell
# 1. Verifier l'etat des GPUs
python scripts/genai-stack/check_vram.py

# 2. Demarrer la stack
.\scripts\genai-stack\manage-genai-stack.ps1 -Action start

# 3. Valider l'authentification
python scripts/genai-stack/validate_stack.py --auth-only

# 4. Lister les noeuds disponibles
python scripts/genai-stack/list_nodes.py

# 5. Executer un workflow de test
python scripts/genai-stack/validate_stack.py --nunchaku

# 6. Arreter la stack
.\scripts\genai-stack\manage-genai-stack.ps1 -Action stop
```

### Premier Deploiement

```bash
# 1. Telecharger les modeles (choisir selon VRAM disponible)
python scripts/genai-stack/download_nunchaku_model.py  # 4GB VRAM
# OU
python scripts/genai-stack/download_qwen_models.py      # 29GB VRAM

# 2. Initialiser l'authentification
python scripts/genai-stack/core/auth_manager.py init

# 3. Deployer
python scripts/genai-stack/core/deploy_comfyui_auth.py

# 4. Valider
python scripts/genai-stack/validate_stack.py --full
```

---

**Derniere mise a jour**: 2026-02-01
**Version**: 2.0.0 (Consolidation Phase)
