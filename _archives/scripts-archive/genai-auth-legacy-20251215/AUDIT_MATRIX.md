# Matrice d'Audit de Consolidation - GenAI Auth

Ce document trace l'analyse exhaustive de chaque script archivé vers sa nouvelle destination consolidée.

**Légende :**
- ✅ : Fonctionnalité entièrement migrée
- ⚠️ : Fonctionnalité migrée partiellement ou différemment (à vérifier)
- ❌ : Fonctionnalité manquante (ACTION REQUISE)
- 🗑️ : Fonctionnalité obsolète/supprimée volontairement

## 1. Core Legacy (`scripts/genai-auth/archive/core_legacy/`)

| Script Source | Fonctionnalité Clé | Destination | Statut | Notes |
| :--- | :--- | :--- | :--- | :--- |
| `cleanup_comfyui_auth.py` | Stop Container | `docker_manager.py` | ⚠️ | Manque option `--force` / `rm` |
| | Clean Volumes (Deep) | - | ❌ | Suppression physique workspace non gérée |
| | Reset Auth Config | - | ❌ | Suppression tokens non gérée |
| `deploy_comfyui_auth.py` | Check Prerequis | `docker_manager.py` | ✅ | |
| | Sync Tokens | `auth_manager.py` | ✅ | |
| | Start Container | `docker_manager.py` | ✅ | |
| | Wait Loop (Curl) | `docker_manager.py` | ✅ | Réintégré via `wait_for_service` |
| | Install Login Node | `docker_manager.py` | ✅ | Via `setup_infrastructure` |
| `diagnose_comfyui_auth.py` | Container Status | `docker_manager.py` | ✅ | |
| | Check Internal Deps | `diagnostic_manager.py` | ✅ | Réintégré |
| | Check Logs Errors | `diagnostic_manager.py` | ✅ | Réintégré |
| | Check Web/API Auth | `validation_suite.py` | ⚠️ | Vérification basique seulement |
| | Fix Missing Deps | - | ❌ | Auto-réparation non migrée |
| `install_comfyui_login.py` | Install Login Node | `docker_manager.py` | ✅ | |
| | Install Qwen Bridge | `docker_manager.py` | ✅ | |
| | Sync Credentials | `auth_manager.py` | ✅ | |
| | Restart Docker | `docker_manager.py` | ✅ | |
| | Validate Nodes | `validation_suite.py` | ⚠️ | Moins verbeux sur les manquants |
| | Test Image Gen | `validation_suite.py` | ⚠️ | Workflow Z-Image utilisé, pas Qwen |
| `setup_complete_qwen.py` | **Download Models** | `docker_manager.py` | ✅ | Réintégré via `download_models` |
| | **Install HF Hub** | `docker_manager.py` | ✅ | Réintégré |
| | **Copy Workflows** | - | ❌ | Copie des JSON workflows non gérée |
| `sync_comfyui_credentials.py` | Sync Logic | `auth_manager.py` | ✅ | |
| | Guest Mode | `auth_manager.py` | ⚠️ | Vérifier implémentation touch/rm |
| `validate_comfyui_auth.py` | Test Auth Endpoints | `validation_suite.py` | ✅ | |
| `validate_genai_ecosystem.py` | Check Structure | `validation_suite.py` | ✅ | |
| | **Check Notebooks** | - | ❌ | Liste exhaustive des notebooks non vérifiée |
| | **Check Docs** | - | ❌ | Présence documentation non vérifiée |
| | **Check BOM/JSON** | - | ❌ | Qualité fichiers (UTF-8 BOM, Valid JSON) perdue |

## 2. Utils Legacy (`scripts/genai-auth/archive/utils_legacy/`)

| Script Source | Fonctionnalité Clé | Destination | Statut | Notes |
| :--- | :--- | :--- | :--- | :--- |
| `comfyui_client_helper.py` | API Client | `comfyui_client.py` | ✅ | |
| `consolidated_tests.py` | Test Runner | `validation_suite.py` | ✅ | |
| `debug_proxy.py` | Proxy Debug | - | 🗑️ | Outil dev ponctuel, non critique |
| `diagnostic_model_paths.py` | Check Paths | - | ❌ | Vérification physique des modèles sur disque |
| `diagnostic_utils.py` | System Info | `validation_suite.py` | ⚠️ | Infos système partielles |
| `docker_qwen_manager.py` | Docker Ops | `docker_manager.py` | ✅ | |
| `genai_auth_manager.py` | Auth Logic | `auth_manager.py` | ✅ | |
| `reconstruct_env.py` | Env Regen | `auth_manager.py` | ✅ | |
| `test_forge_connectivity.py` | Forge Check | `validation_suite.py` | ✅ | |
| `token_manager.py` | Token CRUD | `auth_manager.py` | ✅ | |
| `token_synchronizer.py` | Sync Logic | `auth_manager.py` | ✅ | |
| `validate_all_models.py` | Check Models | `validation_suite.py` | ⚠️ | Vérifie via API, pas fichier |
| `validate_gpu_cuda.py` | Nvidia-smi | `docker_manager.py` | ✅ | |
| `workflow_utils.py` | JSON Handling | `comfyui_client.py` | ✅ | |

## 3. Scripts Épars (`scripts/genai-auth/archive/scripts_epars/`)

| Script Source | Fonctionnalité Clé | Destination | Statut | Notes |
| :--- | :--- | :--- | :--- | :--- |
| `*_notebook_*.py` | Notebook Utils | - | 🗑️ | Obsolète (Notebooks gérés ailleurs) |
| `fix-qwen-diffusers-paths.py` | Path Fix | - | ❌ | Patch spécifique Qwen Diffusers (critique ?) |
| `benchmark_*.py` | Benchmarks | - | 🗑️ | Non critique pour le run |
| `inspect_*.py` | Node Inspection | `validation_suite.py` | ✅ | Couvert par `check_custom_nodes` |

## 4. Scripts Racine Archivés (`scripts/genai-auth/archive/`)

| Script Source | Fonctionnalité Clé | Destination | Statut | Notes |
| :--- | :--- | :--- | :--- | :--- |
| `comfyui-auth-resolution-summary.ps1` | Rapport | - | 🗑️ | Doc |
| `finalize_mission.ps1` | Git Ops | - | 🗑️ | Process |
| `monitor_comfyui_qwen.ps1` | Monitoring | `docker_manager.py` | ✅ | Via `logs -f` ou `status` |
| `restore-env-comfyui.ps1` | Restore | - | ❌ | Script de restauration d'environnement |
| `run-comfyui-auth-diagnostic.ps1` | Diag Wrapper | `manage-genai.ps1` | ✅ | Action `Diagnose` |
| `setup-comfyui-auth.ps1` | Setup Wrapper | `manage-genai.ps1` | ✅ | Action `Setup` |

---

**ACTIONS PRIORITAIRES IDENTIFIÉES :**

1.  [ ] **`fix-qwen-diffusers-paths.py`** : Vérifier si ce patch est encore nécessaire. Si oui, l'intégrer dans `setup_infrastructure`.
2.  [ ] **`diagnostic_model_paths.py`** : Intégrer la vérification des chemins de modèles dans `validation_suite.py` (Static Check).
3.  [ ] **Copy Workflows** : Ajouter la copie des workflows JSON par défaut dans `setup_infrastructure`.
4.  [ ] **Clean Volumes** : Ajouter une option `--deep` à `prune` dans `docker_manager.py` pour supprimer le workspace si demandé.
5.  [ ] **Static Quality Checks** : Réintégrer `check_notebooks_bom` et `check_notebooks_valid_json` dans `validation_suite.py`.