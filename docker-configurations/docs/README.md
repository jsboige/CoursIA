# Docker Configurations - Documentation Complète

## Vue d'ensemble

Ce répertoire contient l'ensemble des configurations Docker pour les services d'IA générative, organisées selon une structure standardisée pour faciliter la maintenance et le déploiement.

## Structure des répertoires

```
docker-configurations/
├── services/           # Services Docker actifs
│   ├── comfyui-qwen/    # Service ComfyUI avec modèle Qwen
│   ├── orchestrator/      # Service d'orchestration central
│   └── development/       # Environnements de développement
├── shared/             # Volumes partagés entre services
│   ├── models/           # Modèles d'IA (partagés)
│   ├── cache/            # Cache temporaires (partagé)
│   └── outputs/          # Sorties générées (partagées)
├── archive/            # Configurations archivées par date
│   └── 2025-11-26/    # Archive du 26 novembre 2025
└── docs/              # Documentation
    └── README.md         # Ce fichier
```

## Services disponibles

### 1. ComfyUI-Qwen

Service ComfyUI préconfiguré avec le modèle Qwen pour la génération d'images.

**Emplacement :** `services/comfyui-qwen/`

**Fichiers principaux :**
- `docker-compose.yml` : Configuration Docker Compose
- `.env` : Variables d'environnement (à créer depuis `.env.example`)
- `README.md` : Documentation spécifique au service

**Volumes partagés utilisés :**
- `../shared/models` → `/workspace/ComfyUI/models`
- `../shared/cache` → `/workspace/ComfyUI/cache`
- `../shared/outputs` → `/workspace/ComfyUI/output`

**Démarrage :**
```bash
cd services/comfyui-qwen
docker-compose up -d
```

### 2. Orchestrator

Service central d'orchestration pour gérer multiples services d'IA.

**Emplacement :** `services/orchestrator/`

**Fichiers principaux :**
- `docker-compose.yml` : Configuration Docker Compose avec 3 services
- `Dockerfile` : Image Docker de l'orchestrateur
- `orchestrator.py` : Logique d'orchestration
- `requirements.txt` : Dépendances Python

**Services gérés :**
- `flux-1-dev` : Service Flux v1 (développement)
- `stable-diffusion-35` : Service Stable Diffusion 3.5
- `comfyui-workflows` : Service de workflows ComfyUI

**Démarrage :**
```bash
cd services/orchestrator
docker-compose up -d
```

**API de l'orchestrateur :**
- Port : 8000
- Endpoints disponibles :
  - `GET /` : Statut des services
  - `GET /services` : Liste des services
  - `POST /services/{service_name}/start` : Démarrer un service
  - `POST /services/{service_name}/stop` : Arrêter un service

## Volumes partagés

### Models (`shared/models/`)

Contient les modèles d'IA partagés entre tous les services.

**Structure :**
```
shared/models/
├── qwen/          # Modèles Qwen
├── flux/           # Modèles Flux
├── stable-diffusion/ # Modèles Stable Diffusion
└── .gitkeep        # Fichier pour maintenir le répertoire dans Git
```

### Cache (`shared/cache/`)

Cache temporaire partagé entre les services pour optimiser les performances.

**Structure :**
```
shared/cache/
└── .gitkeep        # Fichier pour maintenir le répertoire dans Git
```

### Outputs (`shared/outputs/`)

Répertoire de sortie partagé pour les fichiers générés par les services.

**Structure :**
```
shared/outputs/
└── .gitkeep        # Fichier pour maintenir le répertoire dans Git
```

## Archive

Les configurations obsolètes sont archivées par date dans le répertoire `archive/`.

**Structure actuelle :**
```
archive/2025-11-26/
├── comfyui-workflows/          # Ancienne configuration ComfyUI workflows
├── flux-1-dev/               # Ancienne configuration Flux
├── stable-diffusion-35/        # Ancienne configuration SD3.5
├── docker-compose-no-auth.yml  # Configuration sans authentification
├── docker-compose.yml.backup-*  # Sauvegardes automatiques
├── docker-compose.yml.obsolete # Configuration obsolète
├── .env.backup-SECURE        # Sauvegarde sécurisée des variables
└── README.md                 # Documentation de l'archive
```

## Procédures d'exploitation

### Démarrage des services

1. **Service ComfyUI-Qwen :**
   ```bash
   cd docker-configurations/services/comfyui-qwen
   cp .env.example .env  # Éditer les variables si nécessaire
   docker-compose up -d
   ```

2. **Service Orchestrator :**
   ```bash
   cd docker-configurations/services/orchestrator
   docker-compose up -d
   ```

### Arrêt des services

```bash
# Pour un service spécifique
docker-compose down

# Pour tous les services
docker-compose down --remove-orphans
```

### Surveillance des services

1. **Vérifier l'état des conteneurs :**
   ```bash
   docker-compose ps
   ```

2. **Voir les logs :**
   ```bash
   docker-compose logs -f [service_name]
   ```

3. **API de l'orchestrateur :**
   ```bash
   curl http://localhost:8000/services
   ```

### Maintenance

1. **Nettoyage des volumes :**
   ```bash
   # Vider le cache (avec précaution)
   docker-compose exec service_name rm -rf /workspace/cache/*
   
   # Nettoyer les outputs anciens
   find shared/outputs/ -type f -mtime +7 -delete
   ```

2. **Mise à jour des modèles :**
   ```bash
   # Copier les nouveaux modèles dans le volume partagé
   cp /path/to/new/model shared/models/
   ```

## Sécurité

### Variables d'environnement

- Ne jamais commiter les fichiers `.env` contenant des secrets
- Utiliser `.env.example` comme template
- Archiver les anciennes configurations avec `.backup` avant modification

### Gestion des tokens

- Les tokens d'authentification sont archivés dans `archive/`
- Utiliser des tokens temporaires pour le développement
- Regénérer les tokens régulièrement en production

### Permissions

- Assurer les permissions appropriées sur les volumes partagés
- Vérifier que les conteneurs peuvent écrire dans `shared/outputs`
- Limiter l'accès en lecture seule pour `shared/models` si nécessaire

## Dépannage

### Problèmes courants

1. **Volumes non montés :**
   - Vérifier les chemins relatifs dans `docker-compose.yml`
   - S'assurer que les répertoires `shared/` existent

2. **Services ne démarrent pas :**
   - Vérifier les ports déjà utilisés
   - Consulter les logs avec `docker-compose logs`

3. **Permissions denied :**
   - Vérifier les permissions sur les volumes partagés
   - Exécuter avec `sudo` si nécessaire

### Commandes utiles

```bash
# Reconstruire les images
docker-compose build --no-cache

# Forcer la recréation des conteneurs
docker-compose up -d --force-recreate

# Nettoyer les ressources non utilisées
docker system prune -f
```

## Contact et support

Pour toute question ou problème concernant ces configurations :

1. Consulter la documentation spécifique à chaque service
2. Vérifier les logs des services concernés
3. Consulter l'archive pour les configurations précédentes

---

**Dernière mise à jour :** 26 novembre 2025  
**Version :** 1.0.0