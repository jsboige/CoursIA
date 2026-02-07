# Archive - Scripts Legacy GenAI Stack

Ce repertoire contient les fichiers archives lors de la consolidation de fevrier 2026.
Ces fichiers sont conserves pour reference mais ne sont plus utilises activement.

## Pourquoi ces fichiers sont archives

La consolidation a remplace ~35 scripts eparpilles par un CLI unifie `genai.py` avec 6 modules
(`commands/docker.py`, `commands/validate.py`, `commands/notebooks.py`, `commands/models.py`,
`commands/gpu.py`, `commands/auth.py`) et une configuration partagee (`config.py`).

## Fichiers depuis core/

| Fichier | Raison | Remplace par |
|---------|--------|-------------|
| `validate_mission_documentation.py` | Valide des docs de mission nov 2025 inexistantes | - |
| `test_correction_setup_complete.py` | Importe `setup_complete_qwen` inexistant (CASSE) | - |
| `diagnose_comfyui_auth.py` | Importe `docker_qwen_manager` inexistant (CASSE) | `genai.py auth audit` |
| `deploy_comfyui_auth.py` | Deploiement one-shot | `genai.py docker start` |
| `cleanup_comfyui_auth.py` | Nettoyage one-shot | `genai.py auth` |
| `validate_genai_ecosystem.py` | 873 lignes, chevauche validate.py | `genai.py validate --full` |

## Fichiers depuis utils/ (tout le repertoire)

| Fichier | Raison | Remplace par |
|---------|--------|-------------|
| `comfyui_client_helper.py` | 1418 lignes, remplace par core/comfyui_client.py (269 lignes) | `core/comfyui_client.py` |
| `validate_genai_stack.py` | Remplace par validate_stack.py puis commands/validate.py | `genai.py validate` |
| `validate_mission_documentation.py` | DOUBLON EXACT de core/ | - |
| `token_manager.py` | Remplace par core/auth_manager.py | `genai.py auth` |
| `token_synchronizer.py` | Remplace par core/auth_manager.py sync | `genai.py auth sync` |
| `validate_tokens_simple.py` | Remplace par core/auth_manager.py audit | `genai.py auth audit` |
| `reconstruct_env.py` | Remplace par core/auth_manager.py reconstruct-env | `genai.py auth reconstruct-env` |
| `consolidated_tests.py` | Importe token_manager + comfyui_client_helper (legacy) | `genai.py validate` |
| `diagnostic_utils.py` | Jamais appele depuis aucun script actif | - |
| `diagnostic_model_paths.py` | Script one-shot Phase 29, probleme resolu | - |
| `validate_all_models.py` | Remplace par validate_stack.py --full | `genai.py validate --full` |
| `benchmark.py` | Hardcode login/password, auth par cookie obsolete | - |
| `workflow_utils.py` | Remplace par core/comfyui_client.py WorkflowManager | `core/comfyui_client.py` |
| `validate_gpu_cuda.py` | Absorbe dans commands/gpu.py | `genai.py gpu --detailed` |
| `test_forge_connectivity.py` | Absorbe dans commands/validate.py | `genai.py validate --check-forge` |
| `test_forge_notebook.py` | 3 lignes papermill | `genai.py notebooks` |
| `debug_proxy.py` | Proxy debug ponctuel | - |
| `docker-setup.ps1` | Remplace par docker_manager.py/genai.py docker | `genai.py docker start` |
| `docker-start.ps1` | Remplace par docker_manager.py/genai.py docker | `genai.py docker start` |
| `docker-stop.ps1` | Remplace par docker_manager.py/genai.py docker | `genai.py docker stop` |

## Fichier depuis racine

| Fichier | Raison | Remplace par |
|---------|--------|-------------|
| `manage-genai-stack.ps1` | PowerShell remplace par Python multi-plateforme | `genai.py docker` |

## Date d'archivage

Fevrier 2026 - Consolidation genai-stack
