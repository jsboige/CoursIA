# Docker Configurations - GenAI Ecosystem

Ce répertoire contient les configurations Docker consolidées pour l'écosystème GenAI Images, en parfaite cohérence avec les scripts `genai-auth`.

## 📁 Structure Organisée

```
docker-configurations/
├── README.md                    (ce fichier)
├── _archive-20251125/          (configurations obsolètes archivées)
├── cache/                       (cache partagé pour tous les services)
├── models/                      (modèles partagés pour tous les services)
├── orchestrator/                (service d'orchestration)
└── comfyui-qwen/              (configuration principale ComfyUI + Qwen)
    ├── README.md
    ├── docker-compose.yml
    ├── .env.example
    ├── install_comfyui.sh
    └── workspace/
```

## 🚀 Configuration Principale

### `comfyui-qwen/` - ComfyUI + Qwen Image-Edit

Configuration principale et fonctionnelle pour ComfyUI avec le modèle Qwen-Image-Edit-2509-FP8.

**Caractéristiques** :
- ✅ **Authentification ComfyUI-Login** consolidée (Phase 29)
- ✅ **GPU RTX 3090** optimisé (24GB VRAM)
- ✅ **Scripts genai-auth** intégrés et validés
- ✅ **Modèles FP8 officiels** Comfy-Org
- ✅ **Documentation complète** et procédures de dépannage

**Démarrage rapide** :
```bash
cd docker-configurations/comfyui-qwen
cp .env.example .env
# Éditer .env avec vos configurations
docker-compose up -d
```

**Accès** : http://localhost:8188 (avec authentification)

## 🔧 Services Complémentaires

### `orchestrator/` - Service d'Orchestration

Service Python pour la gestion et l'orchestration des conteneurs GenAI.

**Fonctionnalités** :
- Monitoring des ressources (CPU, GPU, mémoire)
- Gestion du cycle de vie des conteneurs
- API REST pour l'orchestration
- Intégration avec les scripts genai-auth

### `models/` - Répertoire de Modèles Partagés

Volume partagé pour tous les modèles GenAI.

**Structure** :
```
models/
├── checkpoints/          (modèles principaux)
├── vae/                 (VAE models)
├── unet/                (UNET models)
└── clip/                 (CLIP models)
```

### `cache/` - Cache Partagé

Volume partagé pour le cache des différents services (HuggingFace, CivitAI, etc.).

## 🔗 Intégration avec Scripts GenAI-Auth

Cette configuration est conçue pour fonctionner de manière transparente avec les scripts consolidés :

### Scripts Principaux

- **`setup_complete_qwen.py`** : Installation complète automatisée
- **`validate_genai_ecosystem.py`** : Validation de l'écosystème
- **`diagnose_comfyui_auth.py`** : Diagnostic authentification
- **`install_comfyui_login.py`** : Installation ComfyUI-Login

### Flux de Travail Validé

1. **Installation** : `python scripts/genai-auth/core/setup_complete_qwen.py`
2. **Validation** : `python scripts/genai-auth/core/validate_genai_ecosystem.py`
3. **Diagnostic** : `python scripts/genai-auth/core/diagnose_comfyui_auth.py`
4. **Utilisation** : Accès via http://localhost:8188

## 🗑️ Configurations Archivées

Les configurations obsolètes ont été archivées dans `_archive-20251125/` :
- Anciens docker-compose.yml multi-services
- Configurations incomplètes (flux-1-dev, stable-diffusion-35, comfyui-workflows)
- Fichiers de backup et versions obsolètes

Voir `_archive-20251125/README.md` pour les détails.

## 📋 Prérequis

### Système
- **Docker Desktop** avec support WSL2
- **NVIDIA Docker Runtime** (GPU support)
- **Windows 11** avec WSL2 Ubuntu

### Hardware
- **GPU RTX 3090** (24GB VRAM recommandée)
- **RAM** : 32GB+ recommandé
- **Stockage** : 100GB+ pour les modèles

### Logiciels
- **Python 3.8+** (pour les scripts genai-auth)
- **Git** (pour le clonage des repositories)
- **PowerShell 7+** (pour les scripts Windows)

## 🔒 Sécurité

- **Tokens sécurisés** : Stockés dans `.secrets/` (gitignore)
- **Authentification bcrypt** : ComfyUI-Login avec hash bcrypt
- **Isolation réseau** : Containers isolés sur réseau dédié
- **Volumes read-only** : Modèles montés en lecture seule

## 📚 Documentation Complète

Pour la documentation détaillée de l'écosystème :

- **Scripts GenAI-Auth** : `../scripts/genai-auth/README.md`
- **Rapport Phase 29** : `../docs/suivis/genai-image/RAPPORT-RESOLUTION-UNIFICATION-TOKENS-COMFYUI-20251125.md`
- **Architecture GenAI** : `../docs/genai/`

## 🚨 Dépannage

### Problèmes Communs

1. **Container ne démarre pas** :
   ```bash
   docker-compose logs comfyui-qwen
   ```

2. **GPU non détectée** :
   ```bash
   docker exec comfyui-qwen nvidia-smi
   ```

3. **Authentification échoue** :
   ```bash
   python scripts/genai-auth/core/diagnose_comfyui_auth.py
   ```

4. **Validation complète** :
   ```bash
   python scripts/genai-auth/core/validate_genai_ecosystem.py
   ```

### Support

Pour toute question ou problème :
1. Consulter les logs du container
2. Utiliser les scripts de diagnostic genai-auth
3. Vérifier la documentation Phase 29
4. Consulter les rapports de suivi dans `docs/suivis/`

---

**Dernière mise à jour** : 2025-11-25  
**Version** : 2.0.0 - Structure consolidée  
**Statut** : Production Ready ✅  
**Phase** : Post-consolidation scripts genai-auth