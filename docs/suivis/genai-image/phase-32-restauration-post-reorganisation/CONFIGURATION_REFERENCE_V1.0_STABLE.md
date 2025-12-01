# Configuration de Référence V1.0 Stable - ComfyUI Auth

**Date de Sanctuarisation** : 2025-12-01
**Version** : v1.0-stable
**Tag Git** : `comfyui-auth-v1.0-stable`
**Statut** : VALIDÉ & SÉCURISÉ

Ce document sert de référence absolue pour la reconstruction de l'environnement ComfyUI avec authentification sécurisée. Il capture l'état exact du système au moment de la validation finale.

---

## 1. Architecture Simplifiée

```mermaid
graph TD
    User[Utilisateur] -->|Auth (Login/Token)| ComfyUI[ComfyUI Container]
    ComfyUI -->|Volume Bind| Workspace[./workspace/ComfyUI]
    ComfyUI -->|Volume Bind| Models[../../shared/models]
    ComfyUI -->|Volume Bind| Outputs[../../shared/outputs]
    
    subgraph "Docker Service: comfyui-qwen"
        ComfyUI
        Env[.env Configuration]
    end
    
    subgraph "Authentification"
        LoginNode[Custom Node: ComfyUI-Login]
        Bcrypt[Hash Bcrypt]
        Token[Bearer Token]
    end
    
    ComfyUI --> LoginNode
    Env -->|Injecte| LoginNode
```

---

## 2. Configuration Complète

### 2.1 Fichier `docker-compose.yml` (Validé)

Emplacement : `docker-configurations/services/comfyui-qwen/docker-compose.yml`

```yaml
services:
  comfyui-qwen:
    image: python:3.11
    container_name: comfyui-qwen
    hostname: comfyui-qwen
    
    deploy:
      resources:
        reservations:
          devices:
            - driver: nvidia
              device_ids: ['${GPU_DEVICE_ID:-0}']
              capabilities: [gpu]
    
    ports:
      - "${COMFYUI_PORT:-8188}:8188"
    
    volumes:
      - type: bind
        source: ${COMFYUI_WORKSPACE_PATH:-./workspace}
        target: /workspace/ComfyUI
      - type: bind
        source: ../../shared/models
        target: /workspace/ComfyUI/models
      - type: bind
        source: ../../shared/cache
        target: /workspace/ComfyUI/cache
      - type: bind
        source: ../../shared/outputs
        target: /workspace/ComfyUI/output
      - type: bind
        source: ../../.secrets/qwen-api-user.token
        target: /workspace/ComfyUI/.secrets/qwen-api-user.token
        read_only: true
      - type: bind
        source: ./entrypoint.sh
        target: /entrypoint.sh
    
    environment:
      - CUDA_VISIBLE_DEVICES=${CUDA_VISIBLE_DEVICES:-0}
      - NVIDIA_VISIBLE_DEVICES=${NVIDIA_VISIBLE_DEVICES:-0}
      - PYTHONUNBUFFERED=1
      - PYTHONDONTWRITEBYTECODE=1
      - TZ=${TZ:-Europe/Paris}
      - COMFYUI_PORT=8188
      - COMFYUI_LISTEN=0.0.0.0
      # Tokens pour téléchargement des modèles
      - CIVITAI_TOKEN=${CIVITAI_TOKEN}
      - HF_TOKEN=${HF_TOKEN}
      - QWEN_API_TOKEN=${QWEN_API_TOKEN}
      # Configuration authentification ComfyUI-Login
      - COMFYUI_LOGIN_ENABLED=${COMFYUI_LOGIN_ENABLED:-true}
      - COMFYUI_USERNAME=${COMFYUI_USERNAME}
      - COMFYUI_PASSWORD=${COMFYUI_PASSWORD}
      - COMFYUI_BEARER_TOKEN=${COMFYUI_BEARER_TOKEN}
      - GUEST_MODE_ENABLED=${GUEST_MODE_ENABLED:-false}
      - SECRET_KEY=${SECRET_KEY}
      # Configuration comportement
      - CORS_ENABLED=${CORS_ENABLED:-true}
      - VERBOSE_LOGGING=${VERBOSE_LOGGING:-false}
      - API_TIMEOUT=${API_TIMEOUT:-30}
      - MAX_LOGIN_ATTEMPTS=${MAX_LOGIN_ATTEMPTS:-3}
      - SESSION_EXPIRE_HOURS=${SESSION_EXPIRE_HOURS:-24}
    
    working_dir: /workspace/ComfyUI
    
    entrypoint: ["/bin/bash", "/entrypoint.sh"]
    
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8188/", "--max-time", "10"]
      interval: 30s
      timeout: 10s
      retries: 5
      start_period: 120s
    
    restart: unless-stopped
    
    networks:
      - comfyui-network
    
    labels:
      - "com.myia.service=comfyui-qwen"
      - "com.myia.gpu=rtx-3090"
      - "com.myia.model=qwen-image-edit-2509"
      - "com.myia.phase=production-secure"

networks:
  comfyui-network:
    driver: bridge
    name: comfyui-network

# Les volumes sont maintenant gérés par le système de volumes partagés
# Pas de volumes locaux nécessaires - utilisation des bind mounts vers shared/
```

### 2.2 Fichier `.env` (Structure Validée)

Emplacement : `docker-configurations/services/comfyui-qwen/.env`
**Note** : Les valeurs sensibles sont masquées par `[REDACTED]`.

```ini
# ComfyUI + Qwen Image-Edit Configuration
# Reconstruit le 2025-11-30 pour résoudre les problèmes d'incohérence
# FICHIER MAÎTRE CONSOLIDÉ - SOURCE DE VÉRITÉ UNIQUE

# =============================================================================
# API KEYS FOR MODEL DOWNLOADS
# =============================================================================
CIVITAI_TOKEN=[REDACTED]
HF_TOKEN=[REDACTED]

# =============================================================================
# QWEN API CONFIGURATION
# =============================================================================
QWEN_API_TOKEN=[REDACTED]

# =============================================================================
# GPU CONFIGURATION
# =============================================================================
GPU_DEVICE_ID=0
CUDA_VISIBLE_DEVICES=0
NVIDIA_VISIBLE_DEVICES=0

# =============================================================================
# COMFYUI CORE CONFIGURATION
# =============================================================================
COMFYUI_PORT=8188
COMFYUI_LOGIN_ENABLED=true
COMFYUI_WORKSPACE_PATH=./workspace

# =============================================================================
# SYSTEM CONFIGURATION
# =============================================================================
TZ=Europe/Paris
COMFYUI_URL=http://localhost:8188

# =============================================================================
# AUTHENTICATION CONFIGURATION
# =============================================================================
COMFYUI_USERNAME=admin
COMFYUI_PASSWORD=[REDACTED]
COMFYUI_BEARER_TOKEN=[REDACTED_BCRYPT_HASH]
COMFYUI_API_TOKEN=[REDACTED_BCRYPT_HASH]
COMFYUI_RAW_TOKEN=[REDACTED]
GUEST_MODE_ENABLED=false
SECRET_KEY=[REDACTED]

# =============================================================================
# APPLICATION BEHAVIOR CONFIGURATION
# =============================================================================
CORS_ENABLED=true
VERBOSE_LOGGING=false
API_TIMEOUT=30
MAX_LOGIN_ATTEMPTS=3
SESSION_EXPIRE_HOURS=24
```

### 2.3 Arborescence Clé

```text
docker-configurations/services/comfyui-qwen/
├── .env                      # Configuration (Authentification & Système)
├── docker-compose.yml        # Définition du service
├── entrypoint.sh             # Script de démarrage
└── workspace/
    └── custom_nodes/
        └── ComfyUI-Login/    # LE COMPOSANT CRITIQUE RESTAURÉ
            ├── __init__.py
            ├── login.html
            ├── password.py
            └── pyproject.toml
```

---

## 3. Procédure de Reconstruction (Disaster Recovery)

En cas de perte totale, suivre ces étapes pour restaurer l'environnement à l'état v1.0-stable.

### Étape 1 : Récupération du Code
```bash
git clone <repo_url>
cd CoursIA
git checkout comfyui-auth-v1.0-stable
```

### Étape 2 : Restauration des Secrets
Créer le fichier `docker-configurations/services/comfyui-qwen/.env` en utilisant le modèle ci-dessus et en remplissant les valeurs `[REDACTED]` depuis le gestionnaire de mots de passe sécurisé (KeePass/Bitwarden).

**Points critiques :**
*   `COMFYUI_LOGIN_ENABLED=true`
*   `COMFYUI_BEARER_TOKEN` doit contenir le hash bcrypt complet (commençant par `$2b$12$`).

### Étape 3 : Lancement
```bash
cd docker-configurations/services/comfyui-qwen
docker-compose up -d --build
```

### Étape 4 : Validation
1.  Accéder à `http://localhost:8188`.
2.  Vérifier que la page de login s'affiche.
3.  Se connecter avec `admin` / `<password>`.

---

## 4. Points de Vigilance & Pièges Évités

1.  **Doublons .env** : Le fichier `.env` a été nettoyé pour ne contenir qu'une seule définition par variable. **Ne jamais ajouter de variables en double à la fin du fichier.**
2.  **Custom Node Fantôme** : Le dossier `workspace/custom_nodes/ComfyUI-Login` doit physiquement exister sur l'hôte car il est monté via un bind volume. Si ce dossier est vide, l'auth ne fonctionnera pas.
3.  **Hash Bcrypt** : Le token dans le `.env` **DOIT** être le hash bcrypt, pas le token brut, pour que `ComfyUI-Login` le valide correctement.
4.  **Persistance** : Les modifications faites dans le container (installation de nouveaux nodes) sont persistées dans `./workspace` sur l'hôte.

---

**Document généré par Roo Code - Agent IA**
*Validation finale de la mission ComfyUI-Login*