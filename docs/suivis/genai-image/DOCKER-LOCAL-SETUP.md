# Guide de Configuration Docker Local - Services GenAI

## 📋 Table des Matières

1. [Vue d'Ensemble](#vue-densemble)
2. [Prérequis Système](#prérequis-système)
3. [Installation Docker Desktop](#installation-docker-desktop)
4. [Configuration Initiale](#configuration-initiale)
5. [Déploiement des Services](#déploiement-des-services)
6. [Vérification et Tests](#vérification-et-tests)
7. [Gestion Quotidienne](#gestion-quotidienne)
8. [Troubleshooting](#troubleshooting)
9. [Commandes Utiles](#commandes-utiles)

---

## 🎯 Vue d'Ensemble

Cette documentation décrit la configuration et le déploiement local de l'infrastructure Docker pour les services de génération d'images GenAI du projet CoursIA.

### Architecture des Services

```
┌─────────────────────────────────────────────────────────────┐
│                    Docker Network                           │
│                  (genai-dev-network)                        │
│                   172.20.0.0/16                             │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐    │
│  │ Orchestrator │  │  FLUX.1-dev  │  │  SD 3.5      │    │
│  │   :8193      │  │  (ComfyUI)   │  │  (Diffusers) │    │
│  │              │  │   :8189      │  │   :8190      │    │
│  └──────────────┘  └──────────────┘  └──────────────┘    │
│         │                  │                  │            │
│         └──────────────────┴──────────────────┘            │
│                            │                               │
│                  ┌──────────────┐                          │
│                  │   ComfyUI    │                          │
│                  │  Workflows   │                          │
│                  │   :8191      │                          │
│                  └──────────────┘                          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Services Déployés

| Service | Port | Type | Usage |
|---------|------|------|-------|
| **Orchestrator** | 8193 | API REST | Gestion lifecycle des services |
| **FLUX.1-dev** | 8189 | ComfyUI | Génération créative haute qualité |
| **Stable Diffusion 3.5** | 8190 | FastAPI | Génération polyvalente production |
| **ComfyUI Workflows** | 8191 | ComfyUI | Workflows éducatifs avancés |

---

## 💻 Prérequis Système

### Configuration Minimale

| Composant | Minimum | Recommandé |
|-----------|---------|------------|
| **OS** | Windows 10/11 64-bit | Windows 11 Pro |
| **RAM** | 16 GB | 32 GB+ |
| **GPU** | NVIDIA GTX 1060 (6GB VRAM) | NVIDIA RTX 3080+ (12GB+ VRAM) |
| **Espace Disque** | 50 GB libre | 100 GB+ libre |
| **CPU** | Quad-core | 8+ cores |

### Logiciels Requis

- ✅ **Docker Desktop 4.x+** (avec WSL 2 sur Windows)
- ✅ **PowerShell 7.0+**
- ✅ **NVIDIA GPU Drivers** (version récente)
- ✅ **CUDA Toolkit** (optionnel, inclus dans les images)

### Vérification GPU NVIDIA

```powershell
# Vérifier la présence du GPU
nvidia-smi

# Résultat attendu: Informations sur votre GPU NVIDIA
```

---

## 🐳 Installation Docker Desktop

### Étape 1: Téléchargement

1. Visitez [Docker Desktop pour Windows](https://www.docker.com/products/docker-desktop/)
2. Téléchargez la dernière version stable
3. Exécutez l'installeur `Docker Desktop Installer.exe`

### Étape 2: Configuration WSL 2

Docker Desktop nécessite WSL 2 sur Windows:

```powershell
# Activer WSL 2
wsl --install

# Redémarrer l'ordinateur
# Puis définir WSL 2 comme version par défaut
wsl --set-default-version 2
```

### Étape 3: Configuration Docker Desktop

1. Lancez Docker Desktop
2. Allez dans **Settings** → **General**
   - ✅ Cocher "Use WSL 2 based engine"
   
3. Allez dans **Settings** → **Resources**
   - **Memory**: Allouer au moins 16 GB (recommandé: 24 GB+)
   - **CPUs**: Allouer au moins 4 cores (recommandé: 8+)
   - **Disk image size**: Au moins 50 GB

4. Allez dans **Settings** → **Docker Engine**
   - Ajouter la configuration pour GPU NVIDIA:

```json
{
  "builder": {
    "gc": {
      "defaultKeepStorage": "20GB",
      "enabled": true
    }
  },
  "experimental": false,
  "runtimes": {
    "nvidia": {
      "path": "nvidia-container-runtime",
      "runtimeArgs": []
    }
  }
}
```

5. Cliquez sur **Apply & Restart**

### Étape 4: Validation Installation

```powershell
# Vérifier Docker
docker --version
docker-compose --version

# Tester Docker
docker run hello-world

# Vérifier accès GPU (si disponible)
docker run --rm --gpus all nvidia/cuda:12.1.0-base-ubuntu22.04 nvidia-smi
```

---

## ⚙️ Configuration Initiale

### Étape 1: Cloner le Projet

```powershell
cd D:\Dev
git clone https://github.com/your-org/CoursIA.git
cd CoursIA
```

### Étape 2: Exécuter le Setup

Le script `docker-setup.ps1` configure automatiquement l'environnement:

```powershell
# Exécution du setup complet
.\scripts\docker-setup.ps1

# Ou avec options spécifiques
.\scripts\docker-setup.ps1 -SkipPrerequisites  # Ignorer vérif prérequis
.\scripts\docker-setup.ps1 -SkipBuild          # Ne pas rebuilder images
```

### Étape 3: Configuration Manuelle (si nécessaire)

Si le script automatique échoue, suivez ces étapes:

```powershell
# 1. Créer la structure de répertoires
New-Item -ItemType Directory -Path "docker-configurations/models" -Force
New-Item -ItemType Directory -Path "docker-configurations/outputs" -Force
New-Item -ItemType Directory -Path "docker-configurations/cache" -Force

# 2. Créer le réseau Docker
docker network create --driver bridge --subnet 172.20.0.0/16 genai-dev-network

# 3. Build l'image orchestrator
docker-compose build orchestrator

# 4. Valider la configuration
docker-compose config
```

### Étape 4: Télécharger les Modèles

⚠️ **Important**: Les modèles ne sont pas inclus dans le dépôt Git (trop volumineux).

#### FLUX.1-dev

```powershell
# Télécharger depuis Hugging Face
# Placer dans: docker-configurations/models/

# Fichiers requis:
# - flux1-dev.safetensors (~12GB)
# - ae.safetensors (~335MB)
# - clip_l.safetensors (~246MB)
```

#### Stable Diffusion 3.5

```powershell
# Le modèle sera téléchargé automatiquement depuis Hugging Face
# au premier démarrage (nécessite token HF si modèle privé)
```

---

## 🚀 Déploiement des Services

### Démarrage Rapide

```powershell
# Démarrer tous les services
.\scripts\docker-start.ps1

# Démarrer avec rebuild des images
.\scripts\docker-start.ps1 -Build

# Démarrer et suivre les logs
.\scripts\docker-start.ps1 -Follow
```

### Démarrage Sélectif

```powershell
# Démarrer uniquement FLUX et l'orchestrateur
.\scripts\docker-start.ps1 -Services flux-1-dev,orchestrator

# Démarrer uniquement Stable Diffusion
.\scripts\docker-start.ps1 -Services stable-diffusion-35
```

### Démarrage Manuel

```powershell
# Alternative: Utiliser docker-compose directement
cd D:\Dev\CoursIA

# Démarrer tous les services en arrière-plan
docker-compose up -d

# Démarrer avec logs
docker-compose up

# Démarrer services spécifiques
docker-compose up -d flux-1-dev orchestrator
```

---

## ✅ Vérification et Tests

### 1. Vérifier le Statut des Services

```powershell
# Statut de tous les containers
docker-compose ps

# Statut détaillé
docker ps --format "table {{.Names}}\t{{.Status}}\t{{.Ports}}"
```

### 2. Health Checks

```powershell
# Vérifier la santé de chaque service
docker inspect coursia-orchestrator --format='{{.State.Health.Status}}'
docker inspect coursia-flux-1-dev --format='{{.State.Health.Status}}'
docker inspect coursia-sd35 --format='{{.State.Health.Status}}'
docker inspect coursia-comfyui-workflows --format='{{.State.Health.Status}}'
```

### 3. Tester les APIs

```powershell
# Orchestrator Health Check
Invoke-RestMethod -Uri "http://localhost:8193/health"

# Liste des services via l'orchestrateur
Invoke-RestMethod -Uri "http://localhost:8193/services"

# Tester FLUX ComfyUI (via navigateur)
Start-Process "http://localhost:8189"

# Tester Stable Diffusion 3.5
Invoke-RestMethod -Uri "http://localhost:8190/health"

# Tester ComfyUI Workflows
Start-Process "http://localhost:8191"
```

### 4. Consulter les Logs

```powershell
# Logs de tous les services
docker-compose logs

# Logs d'un service spécifique
docker-compose logs flux-1-dev

# Suivre les logs en temps réel
docker-compose logs -f

# Logs avec timestamps
docker-compose logs -t flux-1-dev

# Dernières 100 lignes
docker-compose logs --tail=100 flux-1-dev
```

---

## 🔧 Gestion Quotidienne

### Arrêter les Services

```powershell
# Arrêt propre de tous les services
.\scripts\docker-stop.ps1

# Arrêt et sauvegarde des logs
.\scripts\docker-stop.ps1 -SaveLogs

# Arrêt et nettoyage complet
.\scripts\docker-stop.ps1 -Clean

# Arrêt forcé (si les services ne répondent pas)
.\scripts\docker-stop.ps1 -Force
```

### Redémarrer un Service

```powershell
# Redémarrer un service spécifique
docker-compose restart flux-1-dev

# Redémarrer avec rebuild
docker-compose up -d --build flux-1-dev
```

### Mettre à Jour les Services

```powershell
# 1. Arrêter les services
.\scripts\docker-stop.ps1

# 2. Pull les dernières images
docker-compose pull

# 3. Rebuild les images personnalisées
docker-compose build --no-cache

# 4. Redémarrer
.\scripts\docker-start.ps1
```

### Accéder à un Container

```powershell
# Shell dans un container
docker exec -it coursia-flux-1-dev /bin/bash

# Commande unique
docker exec coursia-flux-1-dev ls -la /app/models

# Avec l'utilisateur root
docker exec -u root -it coursia-orchestrator /bin/bash
```

---

## 🔍 Troubleshooting

### Problème: Docker daemon n'est pas actif

**Symptôme**: `error during connect: ... Is the docker daemon running?`

**Solution**:
1. Vérifier que Docker Desktop est lancé
2. Redémarrer Docker Desktop
3. Si le problème persiste:
```powershell
# Redémarrer le service Docker
Restart-Service docker
```

### Problème: Erreur "port is already allocated"

**Symptôme**: `Bind for 0.0.0.0:8189 failed: port is already allocated`

**Solution**:
```powershell
# Trouver le processus qui utilise le port
netstat -ano | findstr :8189

# Arrêter le processus (remplacer PID)
Stop-Process -Id <PID> -Force

# Ou changer le port dans .env.docker
# GENAI_PORT_FLUX=8289
```

### Problème: GPU non détecté dans le container

**Symptôme**: Les services GPU ne démarrent pas ou sont lents

**Solution**:
```powershell
# 1. Vérifier NVIDIA drivers sur l'hôte
nvidia-smi

# 2. Installer NVIDIA Container Toolkit
# Suivre: https://docs.nvidia.com/datacenter/cloud-native/container-toolkit/install-guide.html

# 3. Tester l'accès GPU
docker run --rm --gpus all nvidia/cuda:12.1.0-base-ubuntu22.04 nvidia-smi

# 4. Vérifier la config dans docker-compose.yml
# Rechercher "deploy: -> resources: -> reservations: -> devices:"
```

### Problème: Espace disque insuffisant

**Symptôme**: `no space left on device`

**Solution**:
```powershell
# Nettoyer les ressources Docker inutilisées
docker system prune -a --volumes

# Vérifier l'espace disque Docker
docker system df

# Supprimer les images inutilisées
docker image prune -a

# Supprimer les volumes inutilisés
docker volume prune
```

### Problème: Container crashe au démarrage

**Symptôme**: Container s'arrête immédiatement après le démarrage

**Solution**:
```powershell
# 1. Consulter les logs
docker-compose logs flux-1-dev

# 2. Inspecter le container
docker inspect coursia-flux-1-dev

# 3. Vérifier la configuration
docker-compose config

# 4. Tenter un rebuild complet
docker-compose build --no-cache flux-1-dev
docker-compose up -d flux-1-dev
```

### Problème: Health check échoue

**Symptôme**: Service reste en status "unhealthy"

**Solution**:
```powershell
# 1. Vérifier les logs du service
docker-compose logs flux-1-dev

# 2. Tester manuellement le endpoint de health
docker exec coursia-flux-1-dev curl -f http://localhost:8188/system_stats

# 3. Augmenter le temps de démarrage (start_period) dans docker-compose.yml
# healthcheck:
#   start_period: 300s  # Au lieu de 120s
```

### Problème: Modèles non trouvés

**Symptôme**: `Model not found` dans les logs

**Solution**:
```powershell
# 1. Vérifier que les modèles sont dans le bon répertoire
Get-ChildItem -Path "docker-configurations\models" -Recurse

# 2. Vérifier les permissions
icacls "docker-configurations\models"

# 3. Vérifier les volumes montés
docker inspect coursia-flux-1-dev --format='{{.Mounts}}'
```

---

## 📚 Commandes Utiles

### Gestion des Services

```powershell
# Démarrer tous les services
docker-compose up -d

# Arrêter tous les services
docker-compose down

# Redémarrer un service
docker-compose restart <service>

# Voir les logs
docker-compose logs -f <service>

# Statut des services
docker-compose ps

# Reconstruire et redémarrer
docker-compose up -d --build
```

### Monitoring

```powershell
# Statistiques en temps réel
docker stats

# Statistiques d'un container spécifique
docker stats coursia-flux-1-dev

# Consommation disque
docker system df

# Informations détaillées container
docker inspect coursia-orchestrator
```

### Nettoyage

```powershell
# Nettoyer tout (⚠️ ATTENTION: Supprime tout)
docker system prune -a --volumes

# Nettoyer uniquement les images
docker image prune -a

# Nettoyer uniquement les volumes
docker volume prune

# Nettoyer uniquement les containers arrêtés
docker container prune

# Supprimer un volume spécifique
docker volume rm genai-models-dev
```

### Debugging

```powershell
# Shell interactif dans container
docker exec -it coursia-flux-1-dev /bin/bash

# Exécuter une commande
docker exec coursia-flux-1-dev ls -la /app/models

# Copier fichiers depuis/vers container
docker cp coursia-flux-1-dev:/app/logs/error.log ./logs/
docker cp ./config.json coursia-orchestrator:/app/config/

# Voir les processus dans un container
docker top coursia-flux-1-dev

# Voir les changements dans le filesystem
docker diff coursia-orchestrator
```

### Réseau

```powershell
# Lister les réseaux
docker network ls

# Inspecter un réseau
docker network inspect genai-dev-network

# Voir les containers sur un réseau
docker network inspect genai-dev-network --format='{{range .Containers}}{{.Name}} {{.IPv4Address}}{{"\n"}}{{end}}'

# Tester la connectivité entre containers
docker exec coursia-orchestrator ping coursia-flux-1-dev
```

---

## 📖 Ressources Additionnelles

### Documentation Projet

- [Spécifications Docker GenAI](./genai-docker-specs.md)
- [Orchestration Docker](./genai-docker-orchestration.md)
- [Guide de Troubleshooting](./genai-troubleshooting-guide.md)
- [Configuration des Environnements](./genai-environment-configurations.md)

### Documentation Externe

- [Docker Documentation](https://docs.docker.com/)
- [Docker Compose Reference](https://docs.docker.com/compose/compose-file/)
- [NVIDIA Container Toolkit](https://docs.nvidia.com/datacenter/cloud-native/container-toolkit/)
- [ComfyUI Documentation](https://github.com/comfyanonymous/ComfyUI)

---

## 🆘 Support

En cas de problème non résolu par cette documentation:

1. **Consulter les logs détaillés**:
   ```powershell
   .\scripts\docker-stop.ps1 -SaveLogs
   # Les logs sont dans: logs/backup_<timestamp>/
   ```

2. **Créer une issue GitHub** avec:
   - Version Docker Desktop
   - Logs des services concernés
   - Configuration système (RAM, GPU, OS)
   - Étapes pour reproduire le problème

3. **Vérifier les issues existantes** sur le dépôt GitHub

---

**Dernière mise à jour**: 2025-01-08  
**Version**: 1.0.0  
**Auteur**: CoursIA Team