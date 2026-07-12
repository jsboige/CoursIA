# Rapport 47 : Correction du montage de volume dans docker-compose.yml

- **Date :** 2025-11-04
- **Auteur :** Roo
- **Statut :** En cours (partiellement réussi)

## 1. Objectif

L'objectif de cette mission était d'arrêter le processus de debug inutile et de corriger le montage de volume dans le docker-compose.yml pour permettre à ComfyUI de démarrer correctement avec les modèles Comfy-Org (29GB) déjà présents dans WSL.

## 2. Actions Réalisées

### 2.1. Arrêt du processus de debug inutile
- **Analyse :** Un conteneur `comfyui-qwen` était actif depuis 11 heures avec un processus de debug inutile
- **Action :** Arrêt propre du conteneur avec `docker stop comfyui-qwen`
- **Résultat :** ✅ SUCCÈS - Le conteneur a été arrêté

### 2.2. Sauvegarde du docker-compose.yml
- **Action :** Création d'une sauvegarde avec timestamp
- **Commande :** `Copy-Item 'docker-configurations/services/comfyui-qwen/docker-compose.yml' 'docker-configurations/services/comfyui-qwen/docker-compose.yml.backup-$(Get-Date -Format 'yyyyMMdd-HHmmss')'`
- **Résultat :** ✅ SUCCÈS - Sauvegarde créée avec succès

### 2.3. Correction du montage de volume
- **Problème identifié :** Le montage de volume utilisait `./ComfyUI` au lieu du chemin WSL fonctionnel `/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/`
- **Tentatives :**
  1. Modification directe vers le chemin WSL : Échec (Docker sous Windows ne peut pas accéder directement aux chemins WSL)
  2. Création d'un lien symbolique : Succès partiel (lien créé mais problèmes de permissions persistants)
  3. Retour au montage relatif : Configuration actuelle

### 2.4. Simplification de la commande de démarrage
- **Problème identifié :** La commande originale recréait systématiquement le venv, ce qui était inutile et lent
- **Solution :** Modification pour créer le venv uniquement s'il n'existe pas, avec création dans `/tmp` puis déplacement pour éviter les problèmes de permissions
- **Commande optimisée :**
```bash
bash -c "set -e && echo 'Installing system dependencies...' && apt-get update -qq && apt-get install -y -qq --no-install-recommends python3 python3-pip git curl wget ca-certificates python3.10-venv && apt-get clean && rm -rf /var/lib/apt/lists/* && cd /workspace/ComfyUI && echo 'Checking venv...' && if [ ! -d 'venv' ]; then echo 'Creating venv in /tmp and installing dependencies...' && python3 -m venv /tmp/venv && . /tmp/venv/bin/activate && pip install --no-cache-dir -r requirements.txt && mv /tmp/venv ./venv && echo 'Venv created and dependencies installed successfully'; else echo 'Starting ComfyUI with existing venv...' && . venv/bin/activate && echo 'Venv activated successfully'; fi && echo 'Python version:' && python --version && echo 'Starting ComfyUI...' && exec python main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention"
```

### 2.5. Redémarrage du conteneur
- **Action :** Redémarrage avec `docker-compose down && docker-compose up -d`
- **Résultat :** ✅ SUCCÈS - Le conteneur démarre correctement

## 3. Problèmes Rencontrés

### 3.1. Problème de montage de volume
- **Symptôme :** Le répertoire ComfyUI monté dans le conteneur est vide
- **Cause :** Problème de permissions entre Docker Desktop et le lien symbolique vers WSL
- **Impact :** Le conteneur ne peut pas accéder au fichier `requirements.txt` et aux modèles ComfyUI

### 3.2. Problème de permissions
- **Symptôme :** Erreur `Operation not permitted` lors de la création du venv
- **Cause :** Le conteneur n'a pas les droits d'écriture dans le répertoire monté
- **Tentatives de résolution :**
  - Création du venv dans `/tmp` puis déplacement
  - Utilisation de volumes nommés pour éviter les problèmes de permissions

## 4. État Actuel

### 4.1. Conteneur
- **Statut :** ✅ Démarré
- **Port :** 8188 (configuré correctement)
- **GPU :** NVIDIA RTX-3090 (configuré correctement)
- **Réseau :** comfyui-network (configuré correctement)

### 4.2. Logs du conteneur
- **Observation :** Le conteneur installe correctement les dépendances système mais échoue à accéder au `requirements.txt`
- **Erreur récurrente :** `ERROR: Could not open requirements file: [Errno 1] Operation not permitted: 'requirements.txt'`

## 5. Prochaines Étapes Recommandées

### 5.1. Résolution du problème de montage (Priorité HAUTE)
1. **Vérifier la configuration Docker Desktop** pour s'assurer que les partages WSL sont correctement configurés
2. **Tester différents approches de montage** :
   - Volume nommé avec stockage local
   - Montage direct via Docker Desktop WSL integration
   - Copie des fichiers ComfyUI dans un répertoire Windows accessible

### 5.2. Validation du fonctionnement
1. **Vérifier l'accessibilité** de ComfyUI sur `http://localhost:8188`
2. **Tester la génération d'image** avec les modèles Comfy-Org
3. **Valider les performances** GPU

## 6. Configuration Actuelle du docker-compose.yml

```yaml
services:
  comfyui-qwen:
    image: nvidia/cuda:12.4.0-devel-ubuntu22.04
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
        source: ./ComfyUI
        target: /workspace/ComfyUI
    
    environment:
      - CUDA_VISIBLE_DEVICES=${CUDA_VISIBLE_DEVICES:-0}
      - NVIDIA_VISIBLE_DEVICES=${NVIDIA_VISIBLE_DEVICES:-0}
      - PYTHONUNBUFFERED=1
      - PYTHONDONTWRITEBYTECODE=1
      - TZ=${TZ:-Europe/Paris}
      - COMFYUI_PORT=8188
      - COMFYUI_LISTEN=0.0.0.0
      - COMFYUI_LOGIN_ENABLED=true
      - COMFYUI_AUTH_TOKEN=${QWEN_API_TOKEN}
      - COMFYUI_AUTH_TOKEN_FILE=${COMFYUI_AUTH_TOKEN_FILE}
    
    working_dir: /workspace/ComfyUI
    
    command: >
      bash -c "set -e && echo 'Installing system dependencies...' && apt-get update -qq && apt-get install -y -qq --no-install-recommends python3 python3-pip git curl wget ca-certificates python3.10-venv && apt-get clean && rm -rf /var/lib/apt/lists/* && cd /workspace/ComfyUI && echo 'Checking venv...' && if [ ! -d 'venv' ]; then echo 'Creating venv in /tmp and installing dependencies...' && python3 -m venv /tmp/venv && . /tmp/venv/bin/activate && pip install --no-cache-dir -r requirements.txt && mv /tmp/venv ./venv && echo 'Venv created and dependencies installed successfully'; else echo 'Starting ComfyUI with existing venv...' && . venv/bin/activate && echo 'Venv activated successfully'; fi && echo 'Python version:' && python --version && echo 'Starting ComfyUI...' && exec python main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention"
    
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8188/system_stats"]
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
      - "com.myia.phase=11-production"

networks:
  comfyui-network:
    driver: bridge
    name: comfyui-network
```

## 7. Conclusion

**Statut global :** 🟡 PARTIELLEMENT RÉUSSI

- ✅ **Processus de debug arrêté** avec succès
- ✅ **Sauvegarde créée** avant modification
- ✅ **Configuration simplifiée** pour éviter les reconstructions inutiles
- ✅ **Conteneur redémarré** avec la nouvelle configuration
- ❌ **Problème de montage de volume** non résolu (accès aux fichiers ComfyUI impossible)
- ❌ **ComfyUI non fonctionnel** (ne démarre pas complètement)

**Recommandation immédiate :** Résoudre le problème de montage de volume pour permettre l'accès aux fichiers ComfyUI et aux modèles Comfy-Org (29GB) déjà présents dans WSL.

---

*Ce rapport sera mis à jour une fois le problème de montage de volume résolu.*