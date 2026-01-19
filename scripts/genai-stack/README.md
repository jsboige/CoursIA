# GenAI Stack - Scripts de Gestion

Scripts Python et PowerShell pour la gestion de l'infrastructure GenAI (ComfyUI + Forge).

## Structure

```
scripts/genai-stack/
├── manage-genai-stack.ps1     # Script principal de gestion
├── check_vram.py              # Verification VRAM GPUs
├── validate_stack.py          # Suite de validation ComfyUI
├── validate_notebooks.py      # Validation notebooks Jupyter
├── list_models.py             # Liste des modeles disponibles
├── list_nodes.py              # Liste des custom nodes ComfyUI
├── setup_z_image.py           # Installation modele Z-Image
│
├── core/                      # Modules principaux
│   ├── auth_manager.py        # Gestion authentification
│   ├── comfyui_client.py      # Client API ComfyUI
│   ├── deploy_comfyui_auth.py # Deploiement auth
│   ├── cleanup_comfyui_auth.py
│   ├── diagnose_comfyui_auth.py
│   └── validate_genai_ecosystem.py
│
├── utils/                     # Utilitaires
│   ├── docker-setup.ps1       # Setup Docker
│   ├── docker-start.ps1       # Demarrage Docker
│   ├── docker-stop.ps1        # Arret Docker
│   ├── benchmark.py           # Benchmarks performance
│   ├── diagnostic_utils.py    # Outils de diagnostic
│   ├── token_manager.py       # Gestion tokens
│   ├── workflow_utils.py      # Utilitaires workflows
│   └── validate_gpu_cuda.py   # Validation GPU/CUDA
│
├── config/                    # Configuration
│   └── models_config.json     # Config modeles
│
└── workflows/                 # Workflows de test
    ├── workflow_benchmark.json
    ├── workflow_test_simple.json
    ├── workflow_z_image_reboot.json
    └── workflow_z_image_green_apple.json
```

## Script Principal

### manage-genai-stack.ps1

Orchestrateur unifie pour gerer la stack dual-GPU.

```powershell
# Afficher le statut
.\manage-genai-stack.ps1 -Action status

# Demarrer la stack complete
.\manage-genai-stack.ps1 -Action start

# Arreter la stack
.\manage-genai-stack.ps1 -Action stop

# Redemarrer
.\manage-genai-stack.ps1 -Action restart
```

**Fonctionnalites**:
- Gestion des deux conteneurs (comfyui-qwen, forge-turbo)
- Verification VRAM via `check_vram.py`
- Test de connectivite endpoints
- Affichage statut colore

## Validation

### validate_stack.py

Suite de validation complete pour ComfyUI.

```powershell
# Validation complete (auth + nodes + generation)
python validate_stack.py --full

# Test authentification uniquement
python validate_stack.py --auth-only

# Test custom nodes uniquement
python validate_stack.py --nodes-only

# Avec workflow specifique
python validate_stack.py --workflow workflow_z_image_green_apple.json
```

**Tests effectues**:
1. Health check service ComfyUI
2. Authentification Bearer Token
3. Verification 4 noeuds Qwen critiques
4. Execution workflow Z-Image (optionnel)

### check_vram.py

Affiche l'etat memoire des GPUs.

```powershell
python check_vram.py
```

**Sortie exemple**:
```
Index  | Nom                            | Libre / Total (MiB)       | Utilise
--------------------------------------------------------------------------------
0      | NVIDIA GeForce RTX 3080 Ti     | 14000 / 16384 MiB         | 2384 MiB (14.5%)
1      | NVIDIA GeForce RTX 3090        | 20000 / 24576 MiB         | 4576 MiB (18.6%)
```

## Configuration

### core/auth_manager.py

Gestion centralisee de l'authentification ComfyUI.

**Fonctions principales**:
- `load_config()`: Charge la config depuis `.env`
- `get_bearer_token()`: Recupere le token bcrypt
- `validate_token()`: Valide un token contre l'API

### config/models_config.json

Configuration des modeles disponibles:
- Chemins des checkpoints
- Parametres de chargement
- Mappings GPU

## Workflows de Test

| Workflow | Description | VRAM |
|----------|-------------|------|
| `workflow_test_simple.json` | Test basique connectivite | < 1 GB |
| `workflow_benchmark.json` | Benchmark performance | Variable |
| `workflow_z_image_reboot.json` | Test Z-Image standard | ~6 GB |
| `workflow_z_image_green_apple.json` | Test Z-Image avance | ~8 GB |

## Integration Docker

Les scripts interagissent avec les conteneurs definis dans:
- `docker-configurations/services/comfyui-qwen/`
- `docker-configurations/services/forge-turbo/`

**Chemins relatifs utilises**:
```powershell
$RepoRoot = Resolve-Path "$PSScriptRoot/../.."
$ComfyPath = "$RepoRoot/docker-configurations/services/comfyui-qwen/docker-compose.yml"
$ForgePath = "$RepoRoot/docker-configurations/services/forge-turbo/docker-compose.yml"
```

## Dependances Python

```
requests>=2.28.0
websocket-client>=1.4.0
bcrypt>=4.0.0
python-dotenv>=1.0.0
```

## Exemples d'Usage

### Workflow complet de developpement

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
python scripts/genai-stack/validate_stack.py --workflow workflow_z_image_green_apple.json

# 6. Arreter la stack
.\scripts\genai-stack\manage-genai-stack.ps1 -Action stop
```

### Diagnostic en cas de probleme

```powershell
# Diagnostic authentification
python scripts/genai-stack/core/diagnose_comfyui_auth.py

# Validation ecosysteme complet
python scripts/genai-stack/core/validate_genai_ecosystem.py

# Verification GPU/CUDA
python scripts/genai-stack/utils/validate_gpu_cuda.py
```

---

**Derniere mise a jour**: 2025-01-19
**Version**: 1.0.0 (Phase 43)
