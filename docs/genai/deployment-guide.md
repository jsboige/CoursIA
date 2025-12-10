# ComfyUI + Qwen Image-Edit - Guide de Déploiement Production

**Phase**: 30 - Validation et Sanctuarisation  
**Date mise en production**: 10 Décembre 2025  
**GPU**: NVIDIA RTX 3090 (24GB VRAM)  
**Port local**: 8188  
**URL publique**: https://qwen-image-edit.myia.io

---

## Table des Matières

1. [Architecture](#architecture)
2. [Installation](#installation)
3. [Commandes](#commandes)
4. [Tests et Validation](#tests-et-validation)
5. [Monitoring](#monitoring)
6. [Troubleshooting](#troubleshooting)
7. [Métriques](#métriques)
8. [Maintenance](#maintenance)
9. [Sécurité](#sécurité)

---

## Architecture

### Vue d'ensemble

```
┌─────────────────────────────────────────────────────────────┐
│                    Windows Host                              │
│                                                              │
│  ┌────────────────────────────────────────────────────┐    │
│  │  IIS Reverse Proxy                                  │    │
│  │  - qwen-image-edit.myia.io (HTTPS)                 │    │
│  │  - Port 443 → localhost:8188                       │    │
│  └────────────────────────────────────────────────────┘    │
│                           ↓                                  │
│  ┌────────────────────────────────────────────────────┐    │
│  │  Docker Container (comfyui-qwen)                    │    │
│  │  /workspace/ComfyUI/                                │    │
│  │                                                     │    │
│  │  ┌──────────────────────────────────────────┐     │    │
│  │  │  ComfyUI Server                          │     │    │
│  │  │  - Port 8188                             │     │    │
│  │  │  - GPU: RTX 3090 (NVIDIA Container Toolkit)│   │    │
│  │  │  - Model: Qwen-Image-Edit-2509-FP8 (54GB)│     │    │
│  │  │  - Auth: ComfyUI-Login (Bearer Token)    │     │    │
│  │  └──────────────────────────────────────────┘     │    │
│  └────────────────────────────────────────────────────┘    │
│                                                              │
│  ┌────────────────────────────────────────────────────┐    │
│  │  Monitoring & Automation                            │    │
│  │  - manage-genai.ps1 (Unified Script)               │    │
│  │  - Docker Compose (Restart Policy)                 │    │
│  │  - GPU Performance Monitoring                      │    │
│  └────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────┘
```

### Structure Fichiers

```
CoursIA/
├── scripts/genai-auth/
│   ├── manage-genai.ps1               # Script de gestion unifié
│   └── core/                          # Scripts Python core
│       ├── deploy_comfyui_auth.py     # Déploiement
│       ├── validate_comfyui_auth.py   # Validation
│       └── ...
│
├── docker-configurations/services/comfyui-qwen/
│   ├── docker-compose.yml             # Configuration Docker
│   ├── .env                           # Variables d'environnement
│   └── .secrets/                      # Tokens (monté dans conteneur)
│
└── docs/genai/                        # Documentation pérenne
    ├── deployment-guide.md            # Ce fichier
    └── user-guide.md                  # Guide utilisateur
```

### Configuration GPU CRITIQUE

**Mapping GPU (Docker):**
Le conteneur utilise le runtime NVIDIA et expose tous les GPUs.
ComfyUI est configuré pour utiliser le GPU approprié via `CUDA_VISIBLE_DEVICES` si nécessaire, ou par défaut le premier GPU disponible.

### Services Isolés

| Service | GPU | Port | URL | Statut |
|---------|-----|------|-----|--------|
| Forge SD XL Turbo | RTX 3080 Ti (16GB) | 7860 | turbo.stable-diffusion-webui-forge.myia.io | ✅ OPÉRATIONNEL |
| ComfyUI + Qwen | RTX 3090 (24GB) | 8188 | qwen-image-edit.myia.io | ✅ PRODUCTION |

---

## Installation

### Prérequis

- ✅ Docker Desktop & WSL 2 installés
- ✅ Modèle Qwen-Image-Edit-2509-FP8 téléchargé (54GB)
- ✅ IIS avec Application Request Routing (ARR)
- ✅ PowerShell 7+

### Étape 1: Déploiement Automatisé

**Exécution en Administrateur requise**

```powershell
# Naviguer vers le répertoire racine
cd d:\Dev\CoursIA

# Lancer le déploiement
.\scripts\genai-auth\manage-genai.ps1 -Action Deploy
```

**Résultat attendu:**
- Vérification des prérequis
- Synchronisation des tokens d'authentification
- Démarrage du conteneur Docker
- Validation de la disponibilité du service

### Étape 2: Configuration IIS Reverse Proxy

(Si non déjà fait)

```powershell
# Configuration IIS avec HTTPS (Script legacy, à adapter si besoin)
.\docs\suivis\genai-image\phase-12a-production\scripts\setup-iis-reverse-proxy.ps1
```

---

## Commandes

### Gestion Service (via manage-genai.ps1)

```powershell
# Déployer / Mettre à jour
.\scripts\genai-auth\manage-genai.ps1 -Action Deploy

# Forcer le redéploiement (Rebuild)
.\scripts\genai-auth\manage-genai.ps1 -Action Deploy -Force

# Diagnostiquer les problèmes
.\scripts\genai-auth\manage-genai.ps1 -Action Diagnose

# Tenter une réparation automatique
.\scripts\genai-auth\manage-genai.ps1 -Action Diagnose -AutoFix

# Valider l'authentification et l'API
.\scripts\genai-auth\manage-genai.ps1 -Action Validate

# Synchroniser les tokens (si changés)
.\scripts\genai-auth\manage-genai.ps1 -Action Sync
```

### Logs

```powershell
# Voir logs Docker
docker logs -f comfyui-qwen

# Voir logs ComfyUI (interne)
docker exec -it comfyui-qwen cat /workspace/ComfyUI/comfyui.log
```

---

## Tests et Validation

### Test 1: Validation Automatisée

```powershell
.\scripts\genai-auth\manage-genai.ps1 -Action Validate
```

### Test 2: Interface Web

1. Ouvrir https://qwen-image-edit.myia.io
2. S'authentifier avec les credentials (voir `.secrets/comfyui_auth_tokens.conf` ou demander à l'admin)
3. Vérifier que l'interface charge

### Test 3: Génération Image

Via l'interface ComfyUI:
1. Charger un workflow de test
2. Sélectionner modèle Qwen-Image-Edit-2509-FP8
3. Générer une image
4. Vérifier temps de génération (~5-8s pour 512x512)

---

## Monitoring

### Monitoring GPU Temps Réel

```powershell
# Lancer monitoring performance
.\scripts\genai-auth\manage-genai.ps1 -Action Monitor
```

**Alertes automatiques:**
- ⚠️ VRAM > 90%
- 🌡️ Température > 80°C
- 🚨 Les deux conditions en même temps

### Dashboard IIS

1. Ouvrir **Gestionnaire IIS** (inetmgr)
2. Sélectionner site `qwen-image-edit.myia.io`
3. Vérifier:
   - État: Démarré
   - Bindings: HTTP (80) + HTTPS (443)
   - Application Pool: Running

---

## Troubleshooting

### ComfyUI ne démarre pas

**Symptômes:** Timeout, pas de réponse sur port 8188

**Solutions:**

1. **Diagnostiquer:**
```powershell
.\scripts\genai-auth\manage-genai.ps1 -Action Diagnose
```

2. **Vérifier logs Docker:**
```powershell
docker logs comfyui-qwen
```

3. **Redémarrer:**
```powershell
docker restart comfyui-qwen
```

### Problème d'Authentification

**Symptômes:** Erreur 401/403, mot de passe refusé

**Solutions:**

1. **Resynchroniser les tokens:**
```powershell
.\scripts\genai-auth\manage-genai.ps1 -Action Sync
```

2. **Vérifier le fichier de configuration:**
```powershell
Get-Content .secrets/comfyui_auth_tokens.conf
```

### VRAM Saturée

**Symptômes:** Génération échoue, out of memory errors

**Solutions:**

1. **Vérifier VRAM utilisée:**
```powershell
nvidia-smi
```

2. **Redémarrer ComfyUI:**
```powershell
docker restart comfyui-qwen
```

---

## Métriques

### Performance Typique

| Métrique | Valeur | Notes |
|----------|--------|-------|
| **Temps démarrage** | 10-15s | Dépend de la charge système |
| **VRAM idle** | ~1 GB / 24 GB (4%) | Baseline après démarrage |
| **VRAM génération 512x512** | ~12-18 GB (50-75%) | Dépend du workflow |
| **Temps génération 512x512** | 5-8s | Avec Qwen-Image-Edit FP8 |
| **Temps génération 1024x1024** | 15-25s | Utilisation VRAM ~90% |

### Limites Recommandées

- **VRAM:** Ne pas dépasser 90% de manière prolongée
- **Température:** Alertes à 80°C, critique à 85°C
- **Batch size:** Max 2-3 pour 1024x1024, 4-6 pour 512x512
- **Requêtes simultanées:** Max 2 pour éviter saturation VRAM

---

## Maintenance

### Quotidienne

- ✅ Vérifier logs Docker (erreurs)
- ✅ Vérifier monitoring GPU (alertes)

### Hebdomadaire

- ✅ Nettoyer logs anciens
- ✅ Vérifier espace disque Docker
- ✅ Backup configuration (`.env`, `.secrets`)

### Mensuelle

- ✅ **Mise à jour ComfyUI:** (via rebuild Docker)
- ✅ **Mise à jour custom nodes:** (via script interne ou rebuild)
- ✅ **Vérifier certificat SSL**

---

## Sécurité

### Configuration Actuelle

- ✅ **Reverse Proxy IIS:** Pas d'exposition directe ComfyUI
- ✅ **HTTPS:** Certificat SSL valide (*.myia.io)
- ✅ **Réseau:** Local uniquement (myia.io interne)
- ✅ **Authentification:** ComfyUI-Login (Bearer Token)
- ✅ **Isolation:** Docker Container

### Recommandations

1. **Rotation des Tokens:**
   - Changer régulièrement le mot de passe dans `.env` et relancer `Sync`.

2. **Monitoring sécurité:**
   - Surveiller les logs d'accès IIS et Docker.

---

## Support et Contact

### Documentation

- **ComfyUI Official:** https://github.com/comfyanonymous/ComfyUI
- **Qwen Documentation:** https://github.com/QwenLM/Qwen-Image
- **Custom Node:** https://github.com/gokayfem/ComfyUI-QwenImageWanBridge

### Historique Phases

- **Phase 11:** Déploiement ComfyUI + Qwen (Standalone)
- **Phase 12A:** Production Immédiate
- **Phase 30:** Validation et Sanctuarisation Docker (État actuel)

---

**Dernière mise à jour:** 10 Décembre 2025  
**Version:** 2.0.0 (Dockerized)  
**Statut:** 🚀 PRODUCTION READY
