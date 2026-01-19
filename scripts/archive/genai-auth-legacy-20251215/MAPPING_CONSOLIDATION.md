# Mapping de Consolidation des Scripts GenAI-Auth (Final)

Ce document valide l'architecture cible pour la consolidation finale des scripts d'installation de l'écosystème GenAI.

## 1. Architecture Cible Modulaire

L'objectif est de remplacer les scripts monolithiques (`install_comfyui_login.py`, `setup_complete_qwen.py`) par une architecture modulaire pilotée par `manage-genai.ps1`.

| Module Cible | Responsabilité | Scripts Sources à Fusionner |
| :--- | :--- | :--- |
| **`auth_manager.py`** | Gestion des tokens, bcrypt, synchronisation host/container | `core/sync_comfyui_credentials.py`<br>`utils/genai_auth_manager.py`<br>`utils/token_manager.py` |
| **`docker_manager.py`** | Cycle de vie Docker, installation nodes, téléchargement modèles | `core/install_comfyui_login.py` (Parties Docker/Install)<br>`core/setup_complete_qwen.py` (Partie Models)<br>`utils/docker_qwen_manager.py` |
| **`validation_suite.py`** | Checks statiques, healthchecks, tests génération image | `core/install_comfyui_login.py` (Partie Validation)<br>`utils/validate_genai_stack.py`<br>`utils/validate_all_models.py` |
| **`manage-genai.ps1`** | Point d'entrée unique (CLI) pour l'utilisateur | `archive/setup-comfyui-auth.ps1`<br>`archive/run-comfyui-auth-diagnostic.ps1` |

## 2. Plan de Migration Détaillé

### A. Consolidation `docker_manager.py`
Ce module doit devenir le "maître" de l'infrastructure.
- **Action** : Intégrer la logique de téléchargement de modèles FP8 de `setup_complete_qwen.py`.
- **Action** : Intégrer la logique d'installation de `ComfyUI-Login` et `ComfyUI-QwenImageWanBridge` de `install_comfyui_login.py`.
- **Action** : Standardiser les appels Docker (supprimer la dépendance aux commandes WSL directes si possible, ou les encapsuler proprement).

### B. Consolidation `validation_suite.py`
Ce module doit devenir le "juge de paix".
- **Action** : Intégrer la liste des 28 custom nodes attendus de `install_comfyui_login.py`.
- **Action** : Intégrer la logique de test de génération d'image avec timeout et analyse de qualité (pixels noirs).

### C. Nettoyage (Suppression)
Une fois la logique migrée et validée, les scripts suivants seront déplacés dans `scripts/genai-auth/archive/consolidated_20251212/` :

1.  `scripts/genai-auth/core/install_comfyui_login.py` (Monolithe)
2.  `scripts/genai-auth/core/setup_complete_qwen.py` (Monolithe)
3.  `scripts/genai-auth/core/deploy_comfyui_auth.py` (Doublon)
4.  `scripts/genai-auth/core/install_comfyui_with_auth.py` (Sous-script)
5.  `scripts/genai-auth/core/sync_comfyui_credentials.py` (Intégré dans `auth_manager.py`)
6.  `scripts/genai-auth/utils/docker_qwen_manager.py` (Obsolète)
7.  `scripts/genai-auth/utils/validate_all_models.py` (Obsolète)

## 3. Matrice de Fonctionnalités Critiques à Préserver

| Fonctionnalité | Source Actuelle (Meilleure) | Cible |
| :--- | :--- | :--- |
| **Auth Bcrypt** | `core/sync_comfyui_credentials.py` | `auth_manager.py` |
| **Download Modèles FP8** | `core/setup_complete_qwen.py` | `docker_manager.py` |
| **Install Custom Nodes** | `core/install_comfyui_login.py` | `docker_manager.py` |
| **Check 28 Nodes Qwen** | `core/install_comfyui_login.py` | `validation_suite.py` |
| **Fix Permissions Docker** | `core/install_comfyui_login.py` | `docker_manager.py` |
| **Compatibilité WSL** | `core/install_comfyui_login.py` | `docker_manager.py` |

## 4. Instructions Spéciales pour Code Mode

1.  **Ne pas supprimer** les fichiers avant d'avoir confirmé que leur logique est bien dans le nouveau module.
2.  **Tester** chaque module (`python docker_manager.py status`, `python validation_suite.py --mode static`) après modification.
3.  **Mettre à jour** `manage-genai.ps1` pour qu'il utilise les nouvelles classes Python au lieu d'appeler les anciens scripts.