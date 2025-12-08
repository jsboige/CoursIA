# Scripts d'Authentification et Gestion ComfyUI Qwen

Ce répertoire contient l'ensemble des scripts pour gérer l'authentification, l'installation et la maintenance du service ComfyUI Qwen.

## 📂 Structure

```
scripts/genai-auth/
├── core/                       # Scripts principaux (Master scripts)
│   ├── install_comfyui_login.py    # 🚀 Installation complète et configuration
│   ├── validate_genai_ecosystem.py # ✅ Validation de l'écosystème
│   ├── diagnose_comfyui_auth.py    # 🔍 Diagnostic approfondi authentification
│   └── ...
├── utils/                      # Utilitaires partagés
│   ├── token_synchronizer.py       # 🔄 Synchronisation unifiée des tokens
│   ├── comfyui_client_helper.py    # 🛠️ Client API ComfyUI
│   └── ...
└── archive/                    # Scripts obsolètes ou archivés
```

## 🚀 Scripts Principaux

### 1. Installation et Configuration
**Script :** `core/install_comfyui_login.py`
- Installe ComfyUI-Login et ComfyUI-QwenImageWanBridge
- Synchronise les credentials
- Redémarre le conteneur Docker
- Valide l'installation

```bash
python scripts/genai-auth/core/install_comfyui_login.py
```

### 2. Validation de l'Écosystème
**Script :** `core/validate_genai_ecosystem.py`
- Vérifie la structure des fichiers
- Vérifie la configuration (.env, clés API)
- Teste l'authentification Web et API
- Vérifie la qualité des notebooks

```bash
python scripts/genai-auth/core/validate_genai_ecosystem.py --verbose
```

### 3. Synchronisation des Tokens
**Script :** `utils/token_synchronizer.py`
- Unifie les tokens entre .secrets, .env et Docker
- Assure une source de vérité unique

```bash
python scripts/genai-auth/utils/token_synchronizer.py --unify
```

### 4. Diagnostic Authentification
**Script :** `core/diagnose_comfyui_auth.py`
- Analyse approfondie des problèmes d'authentification
- Vérifie les logs, les dépendances et la configuration du conteneur

```bash
python scripts/genai-auth/core/diagnose_comfyui_auth.py
```

## ⚠️ Scripts Obsolètes

Les scripts suivants sont conservés pour référence mais ne doivent plus être utilisés :
- `core/sync_comfyui_credentials.py` (Remplacé par `utils/token_synchronizer.py`)
- `core/setup_complete_qwen.py` (Remplacé par `core/install_comfyui_login.py`)

## 🔐 Gestion des Credentials

La source de vérité unique pour les tokens est : `.secrets/comfyui_auth_tokens.conf`

Pour régénérer ou resynchroniser les tokens :
```bash
python scripts/genai-auth/utils/token_synchronizer.py --unify