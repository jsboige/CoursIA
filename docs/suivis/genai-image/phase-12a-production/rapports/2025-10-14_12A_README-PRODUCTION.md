# ComfyUI + Qwen Image-Edit - Documentation Production

**Phase**: 12A - Production Immédiate  
**Date mise en production**: 2025-10-14  
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
│  │  WSL Ubuntu                                         │    │
│  │  /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/   │    │
│  │                                                     │    │
│  │  ┌──────────────────────────────────────────┐     │    │
│  │  │  ComfyUI Server                          │     │    │
│  │  │  - Port 8188                             │     │    │
│  │  │  - GPU: RTX 3090 (CUDA_VISIBLE_DEVICES=0)│     │    │
│  │  │  - Model: Qwen-Image-Edit-2509-FP8 (54GB)│     │    │
│  │  └──────────────────────────────────────────┘     │    │
│  └────────────────────────────────────────────────────┘    │
│                                                              │
│  ┌────────────────────────────────────────────────────┐    │
│  │  Monitoring & Automation                            │    │
│  │  - Watchdog Script (auto-restart)                  │    │
│  │  - Tâche Planifiée Windows                         │    │
│  │  - GPU Performance Monitoring                      │    │
│  └────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────┘
```

### Structure Fichiers

```
CoursIA/
├── docs/suivis/genai-image/
│   ├── 2025-10-14_12A_start-comfyui-watchdog.ps1      # Watchdog + monitoring
│   ├── 2025-10-14_12A_install-scheduled-task.ps1     # Installation tâche planifiée
│   ├── 2025-10-14_12A_setup-iis-reverse-proxy.ps1    # Configuration IIS
│   ├── 2025-10-14_12A_monitor-gpu-performance.ps1    # Monitoring GPU
│   ├── 2025-10-14_12A_README-PRODUCTION.md           # Ce fichier
│   └── logs/comfyui-production/                       # Logs production
│       ├── startup-YYYY-MM-DD.log                     # Logs démarrage
│       └── gpu-monitoring-YYYY-MM-DD.csv              # Métriques GPU
│
└── D:/Production/                                      # Créé par scripts
    └── qwen-image-edit.myia.io/
        └── web.config                                  # Config reverse proxy

WSL: /home/jesse/SD/workspace/
└── comfyui-qwen/ComfyUI/
    ├── main.py                                         # ComfyUI core
    ├── venv/                                          # Python environment
    ├── models/checkpoints/
    │   └── Qwen-Image-Edit-2509-FP8/                 # Modèle 54GB
    ├── custom_nodes/
    │   └── ComfyUI-QwenImageWanBridge/               # Custom node
    └── comfyui.log                                    # Logs application
```

### Configuration GPU CRITIQUE

**Mapping GPU (PyTorch vs nvidia-smi):**
```
nvidia-smi GPU 0 = PyTorch GPU 1 (RTX 3080 Ti - 16GB) → Forge
nvidia-smi GPU 1 = PyTorch GPU 0 (RTX 3090 - 24GB)    → ComfyUI ✅
```

**Configuration validée:**
```bash
CUDA_VISIBLE_DEVICES=0  # Utilise RTX 3090 en PyTorch
```

### Services Isolés

| Service | GPU | Port | URL | Statut |
|---------|-----|------|-----|--------|
| Forge SD XL Turbo | RTX 3080 Ti (16GB) | 7860 | turbo.stable-diffusion-webui-forge.myia.io | ✅ OPÉRATIONNEL |
| ComfyUI + Qwen | RTX 3090 (24GB) | 8188 | qwen-image-edit.myia.io | ✅ PRODUCTION |

---

## Installation

### Prérequis

- ✅ ComfyUI installé dans WSL Ubuntu
- ✅ Modèle Qwen-Image-Edit-2509-FP8 téléchargé (54GB)
- ✅ Custom node ComfyUI-QwenImageWanBridge installé
- ✅ IIS avec Application Request Routing (ARR)
- ✅ PowerShell 5.1+ ou PowerShell Core 7+

### Étape 1: Installation Tâche Planifiée

**Exécution en Administrateur requise**

```powershell
# Naviguer vers le répertoire des scripts
cd d:\Dev\CoursIA\docs\genai-suivis

# Installer la tâche planifiée
.\2025-10-14_12A_install-scheduled-task.ps1
```

**Résultat attendu:**
```
✅ Tâche planifiée 'ComfyUI-Qwen-Startup' créée avec succès
```

### Étape 2: Configuration IIS Reverse Proxy

**Exécution en Administrateur requise**

```powershell
# Configuration IIS avec HTTPS
.\2025-10-14_12A_setup-iis-reverse-proxy.ps1
```

**Résultat attendu:**
```
✅ Site HTTP créé: http://qwen-image-edit.myia.io
✅ HTTPS configuré avec certificat *.myia.io
✅ Site démarré
```

### Étape 3: Démarrage Initial

```powershell
# Démarrer ComfyUI manuellement la première fois
.\2025-10-14_12A_start-comfyui-watchdog.ps1

# OU via tâche planifiée
Start-ScheduledTask -TaskName "ComfyUI-Qwen-Startup"
```

**Attendre ~60 secondes pour le démarrage**

---

## Commandes

### Gestion Service

```powershell
# Démarrer (via tâche planifiée)
Start-ScheduledTask -TaskName "ComfyUI-Qwen-Startup"

# Arrêter
Stop-ScheduledTask -TaskName "ComfyUI-Qwen-Startup"
wsl bash -c "pkill -f 'python main.py.*8188'"

# Redémarrer
Stop-ScheduledTask -TaskName "ComfyUI-Qwen-Startup"
wsl bash -c "pkill -f 'python main.py.*8188'"
Start-Sleep -Seconds 5
Start-ScheduledTask -TaskName "ComfyUI-Qwen-Startup"

# Statut tâche planifiée
Get-ScheduledTask -TaskName "ComfyUI-Qwen-Startup" | Format-List

# Désinstaller tâche
Unregister-ScheduledTask -TaskName "ComfyUI-Qwen-Startup" -Confirm:$false
```

### Démarrage Manuel

```powershell
# Démarrage simple
.\2025-10-14_12A_start-comfyui-watchdog.ps1

# Démarrage avec monitoring continu
.\2025-10-14_12A_start-comfyui-watchdog.ps1 -monitor
```

### Logs

```powershell
# Voir logs démarrage (temps réel)
Get-Content .\logs\comfyui-production\startup-$(Get-Date -Format 'yyyy-MM-dd').log -Wait

# Voir logs ComfyUI WSL
wsl cat /home/jesse/SD/workspace/comfyui-qwen/comfyui.log

# Analyser logs GPU (dernières 20 lignes)
Import-Csv .\logs\comfyui-production\gpu-monitoring-$(Get-Date -Format 'yyyy-MM-dd').csv | 
    Select-Object -Last 20 | 
    Format-Table
```

---

## Tests et Validation

### Test 1: Service Local

```powershell
# Test endpoint system_stats
curl http://localhost:8188/system_stats

# Résultat attendu: JSON avec infos système
```

### Test 2: Reverse Proxy HTTP

```powershell
# Test via domaine (HTTP)
curl http://qwen-image-edit.myia.io/system_stats
```

### Test 3: Reverse Proxy HTTPS

```powershell
# Test via domaine (HTTPS)
curl https://qwen-image-edit.myia.io/system_stats

# Résultat attendu: JSON identique au test local
```

### Test 4: Interface Web

```powershell
# Ouvrir dans navigateur
Start-Process "https://qwen-image-edit.myia.io"
```

**Validation visuelle:**
- ✅ Interface ComfyUI charge
- ✅ Workflows disponibles
- ✅ Custom nodes visibles
- ✅ Pas d'erreurs console

### Test 5: Génération Image

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
.\2025-10-14_12A_monitor-gpu-performance.ps1
```

**Sortie:**
```
✅ ComfyUI: Opérationnel
✅ [2025-10-14 04:00:00] GPU RTX 3090
   VRAM: 1200/24576 MB (4.9%)
   Temp: 45°C | Util: 5% | Power: 50.2 W
```

**Alertes automatiques:**
- ⚠️ VRAM > 90%
- 🌡️ Température > 80°C
- 🚨 Les deux conditions en même temps

### Vérifier État Processus

```powershell
# Processus ComfyUI actif
wsl bash -c "ps aux | grep 'python main.py.*8188'"

# GPU utilization
wsl nvidia-smi

# Ports ouverts
netstat -ano | findstr :8188
```

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

**Symptômes:** Timeout après 60s, pas de réponse sur port 8188

**Solutions:**

1. **Vérifier logs WSL:**
```powershell
wsl cat /home/jesse/SD/workspace/comfyui-qwen/comfyui.log | tail -n 50
```

2. **Vérifier GPU disponible:**
```powershell
wsl nvidia-smi
# Vérifier que GPU 1 (RTX 3090) est libre
```

3. **Vérifier venv Python:**
```powershell
wsl bash -c "cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI && source venv/bin/activate && python --version"
```

4. **Test démarrage manuel:**
```bash
wsl bash
cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI
source venv/bin/activate
CUDA_VISIBLE_DEVICES=0 python main.py --listen 0.0.0.0 --port 8188
```

### Reverse Proxy ne fonctionne pas

**Symptômes:** Site IIS accessible mais pas de connexion à ComfyUI

**Solutions:**

1. **Vérifier ComfyUI local:**
```powershell
curl http://localhost:8188/system_stats
```

2. **Vérifier web.config:**
```powershell
Get-Content D:\Production\qwen-image-edit.myia.io\web.config
# Vérifier que port est bien 8188
```

3. **Vérifier ARR installé:**
   - IIS Manager > Server > Application Request Routing Cache
   - Si absent: installer ARR via Web Platform Installer

4. **Restart site IIS:**
```powershell
Restart-WebAppPool -Name "qwen-image-edit.myia.io"
Restart-Website -Name "qwen-image-edit.myia.io"
```

### VRAM Saturée

**Symptômes:** Génération échoue, out of memory errors

**Solutions:**

1. **Vérifier VRAM utilisée:**
```powershell
wsl nvidia-smi
```

2. **Redémarrer ComfyUI:**
```powershell
wsl bash -c "pkill -f 'python main.py.*8188'"
Start-Sleep -Seconds 5
.\2025-10-14_12A_start-comfyui-watchdog.ps1
```

3. **Vérifier pas d'autres processus GPU:**
```powershell
wsl bash -c "fuser -v /dev/nvidia1"
```

### Certificat SSL Expiré

**Symptômes:** Erreur HTTPS, avertissement navigateur

**Solutions:**

1. **Vérifier date expiration:**
```powershell
Get-ChildItem Cert:\LocalMachine\My | Where-Object { $_.Subject -like "*myia.io*" } | 
    Format-Table Subject, NotAfter
```

2. **Renouveler certificat** (Let's Encrypt ou autre)

3. **Ré-exécuter setup IIS:**
```powershell
.\2025-10-14_12A_setup-iis-reverse-proxy.ps1
```

### Processus Zombie

**Symptômes:** Port 8188 occupé mais service non réactif

**Solutions:**

```powershell
# Tuer tous processus ComfyUI
wsl bash -c "pkill -9 -f 'python main.py.*8188'"

# Vérifier port libéré
netstat -ano | findstr :8188

# Redémarrer
.\2025-10-14_12A_start-comfyui-watchdog.ps1
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
| **Température idle** | 40-50°C | Ventilation normale |
| **Température charge** | 70-80°C | Génération intensive |
| **Consommation idle** | ~50W | GPU au repos |
| **Consommation pic** | ~300W | Génération active |
| **Latence réseau (reverse proxy)** | <10ms | IIS local |

### Limites Recommandées

- **VRAM:** Ne pas dépasser 90% de manière prolongée
- **Température:** Alertes à 80°C, critique à 85°C
- **Batch size:** Max 2-3 pour 1024x1024, 4-6 pour 512x512
- **Requêtes simultanées:** Max 2 pour éviter saturation VRAM

---

## Maintenance

### Quotidienne

- ✅ Vérifier logs `startup-YYYY-MM-DD.log` (erreurs)
- ✅ Vérifier monitoring GPU (alertes)
- ✅ Tester endpoint `/system_stats`

### Hebdomadaire

- ✅ Nettoyer logs anciens (>7 jours)
```powershell
Get-ChildItem .\logs\comfyui-production\*.log | 
    Where-Object { $_.LastWriteTime -lt (Get-Date).AddDays(-7) } | 
    Remove-Item
```

- ✅ Vérifier espace disque modèles
```powershell
wsl df -h /home/jesse/SD/workspace/comfyui-qwen/
```

- ✅ Backup configuration
```powershell
# Backup web.config
Copy-Item D:\Production\qwen-image-edit.myia.io\web.config `
    -Destination .\backups\web.config.$(Get-Date -Format 'yyyy-MM-dd')
```

### Mensuelle

- ✅ **Mise à jour ComfyUI:**
```bash
wsl bash
cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI
git pull
source venv/bin/activate
pip install -r requirements.txt --upgrade
```

- ✅ **Mise à jour custom nodes:**
```bash
cd custom_nodes/ComfyUI-QwenImageWanBridge
git pull
pip install -r requirements.txt --upgrade
```

- ✅ **Test complet génération** (différents workflows)
- ✅ **Vérifier certificat SSL** (expiration dans 30 jours)
- ✅ **Analyser métriques GPU** (tendances)

### Semestrielle

- ✅ Évaluer migration vers Docker (si pertinent)
- ✅ Auditer sécurité reverse proxy
- ✅ Optimiser workflows fréquents
- ✅ Nettoyer modèles non utilisés

---

## Sécurité

### Configuration Actuelle

- ✅ **Reverse Proxy IIS:** Pas d'exposition directe ComfyUI
- ✅ **HTTPS:** Certificat SSL valide (*.myia.io)
- ✅ **Réseau:** Local uniquement (myia.io interne)
- ⚠️ **Authentification:** NON implémentée

### Recommandations

**Si exposition Internet:**

1. **Implémenter authentification:**
   - Basic Auth via IIS
   - OAuth2/OIDC
   - API Keys

2. **Rate Limiting:**
   - Limiter requêtes par IP
   - IIS Dynamic IP Restrictions

3. **WAF:**
   - Azure Application Gateway
   - Cloudflare

4. **Monitoring sécurité:**
   - Logs IIS
   - Détection anomalies

**Configuration IIS Sécurité:**

```xml
<!-- Ajouter à web.config -->
<system.webServer>
    <security>
        <authentication>
            <basicAuthentication enabled="true" />
        </authentication>
        <ipSecurity allowUnlisted="false">
            <add ipAddress="192.168.0.0" subnetMask="255.255.255.0" allowed="true" />
        </ipSecurity>
    </security>
</system.webServer>
```

---

## Support et Contact

### Documentation

- **ComfyUI Official:** https://github.com/comfyanonymous/ComfyUI
- **Qwen Documentation:** https://github.com/QwenLM/Qwen-Image
- **Custom Node:** https://github.com/gokayfem/ComfyUI-QwenImageWanBridge

### Historique Phases

- **Phase 9:** Investigation Forge + Qwen
- **Phase 10:** Diagnostic Forge SDXL
- **Phase 11:** Déploiement ComfyUI + Qwen (Standalone)
- **Phase 12A:** Production Immédiate (Ce document)
- **Phase 12B:** Notebook Bridge Local/Cloud (À venir)

### Fichiers Référence

- `2025-10-13_11_rapport-final-phase11-comfyui-qwen.md` - Rapport Phase 11
- `2025-10-13_11_checkpoint-semantique-1-comfyui-base.md` - Checkpoint 1
- `2025-10-13_11_checkpoint-semantique-2-standalone-validation.md` - Checkpoint 2
- `docker-configurations/services/comfyui-qwen/README.md` - Config Docker (future)

---

**Dernière mise à jour:** 2025-10-14  
**Version:** 1.0.0  
**Statut:** 🚀 PRODUCTION READY

**Prochaine étape:** Phase 12B - Notebook Bridge pour intégration pédagogique