# Rapport Déploiement Infrastructure IIS pour ComfyUI + Qwen

**Date:** 2025-10-15  
**Phase:** 13 - Déploiement Production  
**Statut:** Partiel - Préparation Infrastructure Complète

## 📋 Résumé Exécutif

Infrastructure IIS reverse proxy préparée pour `qwen-image-edit.myia.io`. La structure de répertoire et la configuration sont en place. Nécessite privilèges administrateur pour finaliser le déploiement IIS/SSL et résoudre les problèmes de démarrage ComfyUI.

## ✅ Réalisations

### 1. Exploration Structure D:\Production

**Objectif:** Identifier le modèle de reverse proxy existant  
**Résultat:** Succès ✅

- Structure analysée: 48 répertoires de sites existants
- Modèle identifié: `turbo.stable-diffusion-webui-forge.myia.io`
- Configuration type: IIS reverse proxy avec web.config ARR
- Port Forge existant: 17861 (GPU RTX 3080 Ti)

### 2. Création Répertoire & Configuration

**Objectif:** Préparer la structure pour qwen-image-edit.myia.io  
**Résultat:** Succès ✅

**Répertoire créé:**
```
D:\Production\qwen-image-edit.myia.io\
├── aspnet_client\
├── web.config (adapté pour ComfyUI)
├── iisstart.htm
└── iisstart.png
```

**web.config adapté:**
- URL backend: `http://localhost:8188/` (ComfyUI)
- Host headers: `qwen-image-edit.myia.io`
- Protocole: HTTP + HTTPS avec forward headers
- Règle: `ReverseProxyInboundRule_ComfyUI`

### 3. Scripts & Documentation Admin

**Objectif:** Préparer commandes pour privilèges administrateur  
**Résultat:** Succès ✅

**Fichiers créés:**
- `2025-10-15_13_create-iis-site-comfyui.ps1` - Script création site IIS
- `2025-10-15_13_commandes-admin-iis.md` - Documentation complète admin

**Commandes documentées:**
1. Création site IIS (port 80 + 443)
2. Génération certificat SSL avec win-acme
3. Association certificat au site
4. Commandes alternatives manuelles

## ⚠️ Problèmes Rencontrés

### 1. Privilèges Administrateur

**Impact:** Bloquant pour IIS/SSL  
**Détails:**
- Création site IIS nécessite admin
- Génération certificat SSL nécessite admin
- Tests reverse proxy impossibles sans site IIS actif

**Workaround:** Documentation complète pour exécution manuelle

### 2. Démarrage ComfyUI

**Impact:** Critique  
**Détails:**
- Script lancé: `2025-10-15_13_start-comfyui.sh`
- PID initial: 4597
- Statut actuel: Processus non trouvé
- Logs: Vides ou inaccessibles

**Causes possibles:**
1. Chemin venv incorrect
2. Dépendances Python manquantes
3. Erreur configuration GPU (CUDA_VISIBLE_DEVICES=0)
4. Problème permissions fichiers WSL

**Action requise:** Investigation logs WSL + test manuel

### 3. Tests HTTP Locaux

**Impact:** Bloquant pour validation  
**Détails:**
- Endpoint: `http://localhost:8188/system_stats`
- Test curl/Invoke-WebRequest: Timeout/No response
- ComfyUI non accessible

## 📊 État Actuel Infrastructure

| Composant | Statut | Détails |
|-----------|--------|---------|
| Répertoire IIS | ✅ Créé | D:\Production\qwen-image-edit.myia.io |
| web.config | ✅ Configuré | Port 8188, domaine correct |
| Site IIS | ⏸️ En attente | Nécessite admin |
| Certificat SSL | ⏸️ En attente | Nécessite admin + win-acme |
| ComfyUI | ❌ Non démarré | Investigation requise |
| Tests locaux | ❌ Échec | ComfyUI non accessible |
| Tests reverse proxy | ⏸️ En attente | Site IIS + ComfyUI requis |

## 🔄 Prochaines Étapes

### Phase A: Debug ComfyUI (Non-Admin)

1. **Vérifier installation ComfyUI**
   ```bash
   cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI
   ls -la main.py venv/
   source venv/bin/activate
   python --version
   pip list | grep -E "torch|comfy"
   ```

2. **Test démarrage manuel (foreground)**
   ```bash
   CUDA_VISIBLE_DEVICES=0 python main.py \
     --listen 0.0.0.0 \
     --port 8188 \
     --preview-method auto \
     --use-split-cross-attention
   ```

3. **Vérifier GPU disponible**
   ```bash
   nvidia-smi
   python -c "import torch; print(torch.cuda.is_available()); print(torch.cuda.device_count())"
   ```

### Phase B: Déploiement IIS (Admin Requis)

1. **Exécuter script création site**
   ```powershell
   # En tant qu'Administrateur
   cd D:\Dev\CoursIA
   .\docs\genai-suivis\2025-10-15_13_create-iis-site-comfyui.ps1
   ```

2. **Générer certificat SSL**
   ```powershell
   # En tant qu'Administrateur
   cd D:\Production\win-acme.v2.2.9.1701.x64.pluggable
   .\wacs.exe
   # Ajouter qwen-image-edit.myia.io au plan www.myia.io
   ```

3. **Vérifier site IIS**
   ```powershell
   Get-Website -Name "qwen-image-edit.myia.io"
   Get-WebBinding -Name "qwen-image-edit.myia.io"
   ```

### Phase C: Tests Validation

1. **Test local ComfyUI**
   ```powershell
   Invoke-WebRequest -Uri "http://localhost:8188/system_stats"
   ```

2. **Test reverse proxy HTTP**
   ```powershell
   Invoke-WebRequest -Uri "http://qwen-image-edit.myia.io/system_stats"
   ```

3. **Test reverse proxy HTTPS**
   ```powershell
   Invoke-WebRequest -Uri "https://qwen-image-edit.myia.io/system_stats"
   ```

### Phase D: Validation Visuelle Playwright

1. **ComfyUI UI**
   - URL: https://qwen-image-edit.myia.io
   - Vérifier: Interface charge, modèles disponibles

2. **Forge UI (non-regression)**
   - URL: https://turbo.stable-diffusion-webui-forge.myia.io
   - Vérifier: Toujours fonctionnel

## 📁 Fichiers Créés

```
docs/suivis/genai-image/
├── 2025-10-15_13_create-iis-site-comfyui.ps1      (Script création IIS)
├── 2025-10-15_13_commandes-admin-iis.md           (Doc admin)
├── 2025-10-15_13_start-comfyui.sh                 (Script démarrage)
└── 2025-10-15_13_rapport-deploiement-iis-comfyui.md (Ce rapport)

D:/Production/
└── qwen-image-edit.myia.io/
    ├── web.config (Configuré pour port 8188)
    ├── aspnet_client/
    ├── iisstart.htm
    └── iisstart.png
```

## 🎯 Objectifs Finaux

- [ ] ComfyUI démarré et accessible sur localhost:8188
- [ ] Site IIS créé avec bindings HTTP/HTTPS
- [ ] Certificat SSL généré et associé
- [ ] Tests HTTP/HTTPS reverse proxy réussis
- [ ] Validation visuelle Playwright des deux UIs
- [ ] Métriques collectées (temps démarrage, VRAM)

## 💡 Recommandations

1. **Debug ComfyUI en priorité** avant déploiement IIS
2. **Tests manuels foreground** pour voir erreurs réelles
3. **Vérifier GPU** RTX 3090 bien accessible (CUDA_VISIBLE_DEVICES=0)
4. **Privilèges admin** nécessaires pour finaliser IIS/SSL
5. **Scripts watchdog** à améliorer (gérer encodage CRLF/LF)

## 📞 Support

- Scripts: `docs/suivis/genai-image/2025-10-15_13_*`
- Doc admin: `2025-10-15_13_commandes-admin-iis.md`
- Config IIS: `D:\Production\qwen-image-edit.myia.io\web.config`

---

**Note:** Infrastructure préparée mais nécessite résolution problèmes ComfyUI + privilèges admin pour finalisation complète.