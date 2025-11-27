# Orchestrator Service - GenAI Ecosystem

Service d'orchestration pour la gestion des conteneurs GenAI et monitoring des ressources.

## 📋 Description

L'orchestrator est un service Python qui fournit :
- **Monitoring des ressources** : CPU, GPU, mémoire, disque
- **Gestion des conteneurs** : Démarrage, arrêt, redémarrage
- **API REST** : Interface pour l'orchestration programmatique
- **Intégration genai-auth** : Compatible avec les scripts consolidés

## 🏗️ Architecture

```
orchestrator/
├── Dockerfile              (construction de l'image)
├── orchestrator.py         (service principal)
├── requirements.txt        (dépendances Python)
├── config/               (configuration)
└── README.md             (ce fichier)
```

## 🚀 Utilisation

### Construction et Démarrage

```bash
# Construction de l'image
docker build -t genai-orchestrator:latest .

# Démarrage du service avec Docker Compose
cd docker-configurations/services/orchestrator
docker-compose up -d
```

### Intégration avec Docker Compose

L'orchestrator utilise maintenant Docker Compose pour gérer les 3 services :
- flux-1-dev
- stable-diffusion-35
- comfyui-workflows

Chaque service utilise les volumes partagés pour les modèles, cache et outputs.

## 🔧 Configuration

### Variables d'Environnement

- `GENAI_ENVIRONMENT` : Environnement (development/production)
- `LOG_LEVEL` : Niveau de logging (DEBUG/INFO/WARN/ERROR)
- `DOCKER_API_VERSION` : Version API Docker (défaut: 1.41)
- `MAX_CONCURRENT_MODELS` : Nombre maximum de modèles concurrents
- `API_AUTH_ENABLED` : Activation authentification API
- `HEALTH_CHECK_INTERVAL` : Intervalle health checks (secondes)
- `METRICS_ENABLED` : Activation des métriques

### Endpoints Services

- `FLUX_URL` : URL service FLUX (interne)
- `SD35_URL` : URL service Stable Diffusion 3.5 (interne)
- `COMFYUI_URL` : URL service ComfyUI (interne)

## 📊 API Endpoints

### Health Check
```
GET /health
```

### Monitoring
```
GET /metrics
GET /containers
GET /resources
```

### Gestion Conteneurs
```
POST /containers/{name}/start
POST /containers/{name}/stop
POST /containers/{name}/restart
GET /containers/{name}/status
```

## 🔍 Intégration Scripts GenAI-Auth

L'orchestrator est conçu pour fonctionner avec les scripts genai-auth :

### Scripts Compatibles

- `docker_qwen_manager.py` : Gestion conteneur ComfyUI Qwen
- `validate_genai_ecosystem.py` : Validation écosystème complet
- `diagnose_comfyui_auth.py` : Diagnostic authentification

### Flux de Travail

1. **Validation** : `validate_genai_ecosystem.py` vérifie tous les services
2. **Monitoring** : L'orchestrator surveille les ressources en continu
3. **Gestion** : `docker_qwen_manager.py` gère le cycle de vie des conteneurs
4. **Diagnostic** : `diagnose_comfyui_auth.py` identifie les problèmes

## 📈 Monitoring

### Métriques Collectées

- **CPU** : Utilisation par conteneur et globale
- **GPU** : VRAM utilisée, température, utilisation
- **Mémoire** : RAM utilisée par conteneur
- **Réseau** : Bande passante entrante/sortante
- **Stockage** : Espace disque utilisé

### Alertes

L'orchestrator peut générer des alertes pour :
- Utilisation GPU > 90%
- Mémoire disponible < 1GB
- Conteneur arrêté inopinément
- Espace disque < 10%

## 🔒 Sécurité

- **Socket Docker read-only** : Accès limité à la surveillance
- **Isolation réseau** : Service sur réseau dédié
- **Authentification optionnelle** : Bearer token pour l'API
- **Logs structurés** : Traçabilité complète des actions

## 🚨 Dépannage

### Logs du Service

```bash
# Logs du conteneur orchestrator
docker logs coursia-orchestrator

# Logs en temps réel
docker logs -f coursia-orchestrator
```

### Diagnostic API

```bash
# Test health check
curl http://localhost:8193/health

# Test métriques
curl http://localhost:8193/metrics
```

### Intégration avec Scripts

```bash
# Validation complète écosystème
python scripts/genai-auth/core/validate_genai_ecosystem.py

# Diagnostic conteneur ComfyUI
python scripts/genai-auth/core/diagnose_comfyui_auth.py

# Gestion manuelle conteneur
python scripts/genai-auth/utils/docker_qwen_manager.py status --container comfyui-qwen
```

## 📚 Dépendances

### Python Requirements

- `docker` : Client Docker API
- `psutil` : Monitoring système
- `flask` : Framework web API
- `pydantic` : Validation données
- `requests` : Client HTTP

### Système

- Docker Engine 20.10+
- Python 3.8+
- Accès socket Docker

---

**Dernière mise à jour** : 2025-11-26
**Version** : 2.0.0 (Migration vers volumes partagés)
**Statut** : Production Ready ✅
**Compatibilité** : Scripts genai-auth Phase 29+

## Migration vers les volumes partagés

L'orchestrateur a été migré vers la nouvelle structure avec volumes partagés :
- Les services utilisent maintenant `../shared/models/` pour les modèles
- Le cache partagé est `../shared/cache/`
- Les sorties sont dirigées vers `../shared/outputs/`

Cette migration permet :
- Partage des ressources entre services
- Optimisation de l'espace disque
- Gestion centralisée des modèles et outputs