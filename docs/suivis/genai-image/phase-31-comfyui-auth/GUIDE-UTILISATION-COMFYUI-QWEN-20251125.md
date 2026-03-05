# Guide d'Utilisation - Écosystème ComfyUI-Qwen Sécurisé

**Date de création** : 2025-11-25  
**Version** : 2.0.0  
**Public cible** : Développeurs, administrateurs système, utilisateurs avancés  
**Prérequis** : Docker Desktop, Python 3.8+, GPU NVIDIA

---

## 🎯 Vue d'Ensemble

Ce guide explique comment utiliser l'écosystème ComfyUI-Qwen avec authentification sécurisée via ComfyUI-Login. L'écosystème est conçu pour être sécurisé, performant et facile à maintenir.

```
┌─────────────────────────────────────────────────────────────────────┐
│                 UTILISATEUR DE L'ÉCOSYSTÈME                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────┐    ┌──────────────────────────┐    │
│  │  Interface Web  │    │  API Clients           │    │
│  │  (Login Form)   │    │  (Python/cURL)        │    │
│  └─────────────────┘    └──────────────────────────┘    │
│           │                        │                  │
│           └─────────────┬──────────┘                  │
│                         │                             │
│                         ▼                             │
│  ┌─────────────────────────────────────────────────────┐     │
│  │           ComfyUI-Qwen (port 8188)          │     │
│  │  ┌─ ComfyUI Core                              │     │
│  │  └─ ComfyUI-Login (auth bcrypt)           │     │
│  └─────────────────────────────────────────────────────┘     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 🚀 Installation Rapide

### Prérequis Système

**Hardware recommandé** :
- **GPU** : NVIDIA RTX 3090 (24GB VRAM) ou équivalent
- **RAM** : 32GB minimum
- **Stockage** : 100GB+ pour les modèles

**Logiciels requis** :
- **Docker Desktop** avec support WSL2
- **Python 3.8+** (pour les scripts genai-auth)
- **Git** (pour le clonage des repositories)
- **PowerShell 7+** (pour les scripts Windows)

### Installation Automatisée

```bash
# 1. Cloner le repository
git clone <repository-url>
cd CoursIA

# 2. Installation complète automatisée
python scripts/genai-auth/core/setup_complete_qwen.py

# 3. Suivre les instructions à l'écran
# Le script va :
#   - Vérifier les prérequis
#   - Démarrer le container Docker
#   - Installer ComfyUI-Login
#   - Télécharger les modèles FP8 (29GB)
#   - Configurer l'authentification
#   - Tester la génération d'images
```

### Installation Manuelle (Alternative)

```bash
# 1. Configuration Docker
cd docker-configurations/services/comfyui-qwen
cp .env.example .env
# Éditer .env avec vos configurations

# 2. Démarrage Docker
docker-compose up -d

# 3. Installation ComfyUI-Login
python scripts/genai-auth/core/install_comfyui_login.py

# 4. Configuration authentification
python scripts/genai-auth/utils/token_synchronizer.py --unify

# 5. Validation
python scripts/genai-auth/core/validate_genai_ecosystem.py
```

---

## 🔐 Configuration de l'Authentification

### Compréhension du Système de Tokens

⚠️ **POINT CRITIQUE** : ComfyUI-Login utilise une implémentation inhabituelle

Le serveur attend le **HASH BCRYPT LUI-MÊME** comme Bearer token, pas le mot de passe brut.

```bash
# INCORRECT (ce que tout le monde pense)
Authorization: Bearer mon_mot_de_passe_brut

# CORRECT (ce que ComfyUI-Login attend réellement)
Authorization: Bearer $2b$12$03f3f6f91f4175e338c314f7bd96ebd3dd834b53c1813d69d830f
```

### Configuration des Tokens

#### 1. Tokens Automatiques (Recommandé)

```bash
# Génération et synchronisation automatique
python scripts/genai-auth/utils/token_synchronizer.py --unify

# Le script va :
#   - Créer un token brut sécurisé
#   - Générer le hash bcrypt correspondant
#   - Synchroniser tous les emplacements
#   - Valider la cohérence
```

#### 2. Tokens Manuels (Avancé)

```bash
# Audit des tokens existants
python scripts/genai-auth/utils/token_synchronizer.py --audit

# Synchronisation depuis configuration existante
python scripts/genai-auth/utils/token_synchronizer.py --sync

# Validation de la cohérence
python scripts/genai-auth/utils/token_synchronizer.py --validate
```

### Fichiers de Configuration

#### `.env` (Principal)
```env
# Token d'API ComfyUI (hash bcrypt)
COMFYUI_API_TOKEN=$2b$12$03f3f6f91f4175e338c314f7bd96ebd3dd834b53c1813d69d830f

# Token brut (référence humaine)
COMFYUI_RAW_TOKEN=coursia-2025

# URL de l'interface ComfyUI
COMFYUI_URL=http://localhost:8188
```

#### `.secrets/comfyui_auth_tokens.conf` (Source de vérité)
```json
{
  "version": "1.0",
  "created_at": "2025-11-25T00:00:00",
  "raw_token": "coursia-2025",
  "bcrypt_hash": "$2b$12$03f3f6f91f4175e338c314f7bd96ebd3dd834b53c1813d69d830f",
  "description": "Configuration unifiée des tokens ComfyUI-Login"
}
```

---

## 🌐 Utilisation de l'Interface Web

### Accès via Navigateur

1. **Ouvrir le navigateur** : http://localhost:8188
2. **Page de login** : Interface ComfyUI-Login s'affiche
3. **Saisir les identifiants** :
   - **Username** : `admin` (configurable)
   - **Password** : Votre mot de passe (configuré dans `.env`)
4. **Accès autorisé** : Interface ComfyUI complète

### Fonctionnalités Web

- **Workflow Editor** : Création et modification de workflows
- **Queue Management** : Surveillance des tâches en cours
- **Image Gallery** : Visualisation des images générées
- **Model Management** : Gestion des modèles chargés
- **Settings** : Configuration de ComfyUI

### Sécurité Web

- **Session persistante** : 24 heures par défaut
- **Protection CSRF** : Tokens anti-CSRF
- **Rate limiting** : 3 tentatives maximum avant blocage
- **Logout automatique** : Inactivité prolongée

---

## 🔧 Utilisation API Clients

### Client Python (Recommandé)

#### Installation du Client

```python
# Le client est inclus dans les scripts genai-auth
from scripts.genai_auth.utils.comfyui_client_helper import ComfyUIClient

# Configuration automatique depuis .env
client = ComfyUIClient()  # Charge automatiquement le token
```

#### Génération d'Image Simple

```python
from scripts.genai_auth.utils.comfyui_client_helper import ComfyUIClient

# Créer le client (token chargé automatiquement depuis .env)
client = ComfyUIClient()

# Génération d'image basique
prompt_id = client.generate_text2image(
    prompt="A beautiful sunset over mountains with a lake",
    width=512,
    height=512,
    steps=20,
    cfg_scale=7.5,
    sampler_name="euler",
    scheduler_name="normal"
)

print(f"✅ Génération lancée : {prompt_id}")

# Surveillance du progrès
while True:
    result = client.get_result(prompt_id)
    if result['status'] == 'completed':
        print(f"✅ Image générée : {len(result['images'])} images")
        break
    elif result['status'] == 'failed':
        print(f"❌ Échec : {result.get('error', 'Erreur inconnue')}")
        break
    else:
        print(f"⏳ En cours : {result.get('progress', 0)}%")
        time.sleep(2)
```

#### Génération avec Workflow Personnalisé

```python
# Charger un workflow personnalisé
workflow = client.load_workflow("mon_workflow.json")

# Personnaliser les paramètres
workflow['1']['inputs']['text'] = "A futuristic city at night"
workflow['3']['inputs']['width'] = 768
workflow['3']['inputs']['height'] = 512

# Soumettre le workflow
prompt_id = client.submit_workflow(workflow)

# Récupérer les résultats
result = client.get_result(prompt_id)
if result['status'] == 'completed':
    # Sauvegarder les images
    for i, image_data in enumerate(result['images']):
        with open(f"output_image_{i}.png", 'wb') as f:
            f.write(image_data)
```

### Client cURL (Tests)

#### Test de Connectivité

```bash
# Test sans authentification (doit retourner 401)
curl -i http://localhost:8188/system_stats

# Test avec authentification (doit retourner 200)
curl -i \
  -H "Authorization: Bearer $2b$12$03f3f6f91f4175e338c314f7bd96ebd3dd834b53c1813d69d830f" \
  http://localhost:8188/system_stats
```

#### Génération d'Image via API

```bash
# Soumettre un workflow
curl -X POST \
  -H "Authorization: Bearer $2b$12$03f3f6f91f4175e338c314f7bd96ebd3dd834b53c1813d69d830f" \
  -H "Content-Type: application/json" \
  -d @workflow.json \
  http://localhost:8188/prompt

# Récupérer le résultat
curl -X GET \
  -H "Authorization: Bearer $2b$12$03f3f6f91f4175e338c314f7bd96ebd3dd834b53c1813d69d830f" \
  http://localhost:8188/history/PROMPT_ID
```

---

## 🔄 Scripts de Validation et Maintenance

### Validation Complète de l'Écosystème

```bash
# Validation complète avec corrections automatiques
python scripts/genai-auth/core/validate_genai_ecosystem.py --verbose --fix

# Génération de rapport JSON
python scripts/genai-auth/core/validate_genai_ecosystem.py --report validation_report.json

# Validation silencieuse (pour CI/CD)
python scripts/genai-auth/core/validate_genai_ecosystem.py --quiet
```

**Validations effectuées** :
- ✅ Structure fichiers et notebooks
- ✅ Configuration (.env, clés API)
- ✅ Connectivité APIs (OpenAI, OpenRouter)
- ✅ Authentification ComfyUI (web et API)
- ✅ Contrôle qualité notebooks (BOM, JSON valide)
- ✅ Unification tokens ComfyUI

### Diagnostic d'Authentification

```bash
# Diagnostic complet avec mode verbeux
python scripts/genai-auth/core/diagnose_comfyui_auth.py --verbose

# Diagnostic rapide (pour monitoring)
python scripts/genai-auth/core/diagnose_comfyui_auth.py --quick
```

**Diagnostics effectués** :
- ✅ Statut conteneur ComfyUI
- ✅ Test connectivité service
- ✅ Validation configuration authentification
- ✅ Analyse logs erreurs
- ✅ Génération rapport diagnostic

### Synchronisation des Tokens

```bash
# Unification complète (audit + sync + validate)
python scripts/genai-auth/utils/token_synchronizer.py --unify

# Audit uniquement
python scripts/genai-auth/utils/token_synchronizer.py --audit

# Validation uniquement
python scripts/genai-auth/utils/token_synchronizer.py --validate

# Synchronisation depuis configuration existante
python scripts/genai-auth/utils/token_synchronizer.py --sync
```

### Benchmark de Performance

```bash
# Benchmark avec authentification
python scripts/genai-auth/utils/benchmark.py

# Benchmark sans authentification (pour comparaison)
python scripts/genai-auth/utils/benchmark.py --no-auth

# Benchmark avec workflow personnalisé
python scripts/genai-auth/utils/benchmark.py --workflow custom_workflow.json

# Benchmark avec monitoring GPU détaillé
python scripts/genai-auth/utils/benchmark.py --monitor-gpu
```

---

## 📊 Monitoring et Dépannage

### Surveillance du Container Docker

```bash
# Vérifier le statut du container
docker ps | grep comfyui-qwen

# Voir les logs en temps réel
docker logs -f comfyui-qwen

# Voir les ressources utilisées
docker stats comfyui-qwen

# Accéder au container (pour débogage)
docker exec -it comfyui-qwen bash
```

### Monitoring GPU

```bash
# Depuis l'hôte (Windows)
nvidia-smi

# Depuis le container Docker
docker exec comfyui-qwen nvidia-smi

# Monitoring continu
docker exec comfyui-qwen watch -n 1 nvidia-smi
```

### Logs Importants

#### Logs ComfyUI
```bash
# Logs du service principal
docker logs comfyui-qwen | grep "ComfyUI"

# Logs d'authentification
docker logs comfyui-qwen | grep "ComfyUI-Login"

# Logs d'erreurs
docker logs comfyui-qwen | grep -i error
```

#### Logs des Scripts

```bash
# Logs du synchroniseur de tokens
python scripts/genai-auth/utils/token_synchronizer.py --audit 2>&1 | tee sync.log

# Logs de validation
python scripts/genai-auth/core/validate_genai_ecosystem.py --verbose 2>&1 | tee validation.log
```

### Problèmes Communs et Solutions

#### 1. Échec d'Authentification (HTTP 401)

**Symptôme** : `{"error": "Authentication required."}`

**Causes possibles** :
- Token incorrect ou obsolète
- Token non synchronisé entre les emplacements
- Format de token incorrect (brut au lieu de hash)

**Solutions** :
```bash
# 1. Resynchroniser les tokens
python scripts/genai-auth/utils/token_synchronizer.py --unify

# 2. Valider la configuration
python scripts/genai-auth/core/diagnose_comfyui_auth.py

# 3. Vérifier le token dans .env
grep COMFYUI_API_TOKEN .env
```

#### 2. Container ne Démarre Pas

**Symptôme** : Container en état `Restarting` ou `Exited`

**Causes possibles** :
- GPU non disponible
- Ports déjà utilisés
- Permissions insuffisantes
- Configuration incorrecte

**Solutions** :
```bash
# 1. Vérifier les logs Docker
docker logs comfyui-qwen

# 2. Vérifier la disponibilité GPU
nvidia-smi

# 3. Vérifier les ports
netstat -an | grep 8188

# 4. Redémarrer avec diagnostic
docker-compose down
docker-compose up -d
```

#### 3. Performance Lente

**Symptôme** : Génération d'images > 30 secondes

**Causes possibles** :
- GPU surchargé
- Modèles non optimisés
- Configuration sous-optimale

**Solutions** :
```bash
# 1. Monitoring GPU
docker exec comfyui-qwen nvidia-smi

# 2. Benchmark de performance
python scripts/genai-auth/utils/benchmark.py --monitor-gpu

# 3. Optimisation des paramètres
# Réduire steps, utiliser sampler plus rapide
```

#### 4. Modèles Non Chargés

**Symptôme** : Erreurs de modèles manquants

**Causes possibles** :
- Téléchargement incomplet
- Chemins incorrects
- Permissions insuffisantes

**Solutions** :
```bash
# 1. Vérifier les modèles dans le container
docker exec comfyui-qwen ls -la /workspace/ComfyUI/models/

# 2. Retélécharger les modèles
python scripts/genai-auth/core/setup_complete_qwen.py --skip-docker --skip-auth --skip-test

# 3. Vérifier les permissions
docker exec comfyui-qwen ls -la /workspace/ComfyUI/models/diffusion_models/
```

---

## 🔒 Bonnes Pratiques de Sécurité

### Gestion des Tokens

1. **Rotation régulière** :
   ```bash
   # Générer un nouveau token tous les 90 jours
   python scripts/genai-auth/utils/token_synchronizer.py --unify
   ```

2. **Stockage sécurisé** :
   - Les tokens sont dans `.secrets/` (protégé par .gitignore)
   - Ne jamais commiter de tokens dans Git
   - Utiliser des variables d'environnement pour les déploiements

3. **Accès limité** :
   - Partager uniquement les tokens nécessaires
   - Utiliser des tokens différents par environnement
   - Révoquer les tokens des utilisateurs quittant

### Sécurité Réseau

1. **Isolation** :
   - ComfyUI accessible uniquement depuis localhost
   - Pas d'exposition directe à Internet
   - Utiliser VPN pour accès distant sécurisé

2. **Monitoring** :
   - Surveiller les logs d'accès
   - Détecter les tentatives d'intrusion
   - Configurer des alertes sur activités suspectes

### Sécurité Système

1. **Mises à jour** :
   - Maintenir Docker à jour
   - Mettre à jour les drivers GPU
   - Appliquer les mises à jour de sécurité

2. **Backups** :
   - Sauvegarder régulièrement les configurations
   - Backuper les modèles critiques
   - Documenter les procédures de restauration

---

## 📈 Performance et Optimisation

### Optimisations GPU

1. **Configuration optimale** :
   ```env
   # Dans docker-configurations/services/comfyui-qwen/.env
   GPU_DEVICE_ID=0
   CUDA_VISIBLE_DEVICES=0
   NVIDIA_VISIBLE_DEVICES=0
   ```

2. **Modèles FP8** :
   - Utilisation des modèles FP8 officiels (29GB vs 58GB)
   - Réduction de 50% de l'utilisation VRAM
   - Performance équivalente avec FP16

3. **Batch processing** :
   ```python
   # Génération multiple en une seule requête
   prompts = ["prompt1", "prompt2", "prompt3"]
   results = client.batch_generate(prompts)
   ```

### Optimisations Réseau

1. **Keep-alive** :
   ```python
   # Configuration du client avec keep-alive
   client = ComfyUIClient(
       base_url="http://localhost:8188",
       keep_alive=True,
       timeout=30
   )
   ```

2. **Compression** :
   ```python
   # Demander des images compressées
   result = client.generate_text2image(
       prompt="A beautiful landscape",
       output_format="jpeg",
       quality=85
   )
   ```

### Optimisations Stockage

1. **Cache hiérarchique** :
   - Cache RAM pour les modèles fréquents
   - Cache SSD pour les modèles récemment utilisés
   - Cache réseau pour les téléchargements

2. **Nettoyage automatique** :
   ```bash
   # Nettoyer le cache périodiquement
   python scripts/genai-auth/utils/cleanup_cache.py --older-than 7d
   ```

---

## 🚀 Déploiement en Production

### Configuration Production

1. **Sécurité renforcée** :
   ```env
   # Dans docker-configurations/services/comfyui-qwen/.env
   GUEST_MODE_ENABLED=false
   MAX_LOGIN_ATTEMPTS=3
   SESSION_EXPIRE_HOURS=8
   VERBOSE_LOGGING=false
   ```

2. **Monitoring avancé** :
   ```yaml
   # Dans docker-compose.yml
   healthcheck:
     test: ["CMD", "curl", "-f", "http://localhost:8188/"]
     interval: 30s
     timeout: 10s
     retries: 3
     start_period: 120s
   ```

3. **Load balancing** (multiple GPUs) :
   ```yaml
   # Configuration pour multi-GPU
   services:
     comfyui-qwen-gpu0:
       environment:
         - GPU_DEVICE_ID=0
         - CUDA_VISIBLE_DEVICES=0
     comfyui-qwen-gpu1:
       environment:
         - GPU_DEVICE_ID=1
         - CUDA_VISIBLE_DEVICES=1
   ```

### CI/CD Integration

1. **Tests automatisés** :
   ```yaml
   # .github/workflows/validate.yml
   name: Validate ComfyUI-Qwen
   on: [push, pull_request]
   jobs:
     validate:
       runs-on: ubuntu-latest
       steps:
         - uses: actions/checkout@v2
         - name: Validate ecosystem
           run: python scripts/genai-auth/core/validate_genai_ecosystem.py
   ```

2. **Déploiement automatisé** :
   ```bash
   # Script de déploiement
   #!/bin/bash
   set -e
   
   echo "🚀 Déploiement ComfyUI-Qwen en production..."
   
   # 1. Mise à jour du code
   git pull origin main
   
   # 2. Validation de l'écosystème
   python scripts/genai-auth/core/validate_genai_ecosystem.py --fix
   
   # 3. Redémarrage des services
   docker-compose down
   docker-compose up -d
   
   # 4. Validation post-déploiement
   python scripts/genai-auth/core/diagnose_comfyui_auth.py
   
   echo "✅ Déploiement terminé avec succès"
   ```

---

## 📚 Références et Ressources

### Documentation Technique

1. **Scripts GenAI-Auth** : `scripts/genai-auth/README.md` (376 lignes)
2. **Architecture Finale** : `ARCHITECTURE-FINALE-COMFYUI-QWEN-20251125.md` (456 lignes)
3. **Rapport Mission** : `RAPPORT-FINAL-MISSION-COMFYUI-LOGIN-20251125.md` (334 lignes)
4. **Docker Configurations** : `docker-configurations/README.md` (170 lignes)

### Scripts Principaux

1. **Installation complète** : `scripts/genai-auth/core/setup_complete_qwen.py`
2. **Validation écosystème** : `scripts/genai-auth/core/validate_genai_ecosystem.py`
3. **Diagnostic authentification** : `scripts/genai-auth/core/diagnose_comfyui_auth.py`
4. **Synchronisation tokens** : `scripts/genai-auth/utils/token_synchronizer.py`

### Ressources Externes

1. **ComfyUI Documentation** : https://docs.comfy.org/
2. **ComfyUI-Login GitHub** : https://github.com/11cafe/ComfyUI-Login
3. **Qwen Model Documentation** : https://huggingface.co/Qwen/Qwen2-VL
4. **Docker Documentation** : https://docs.docker.com/

### Communauté et Support

1. **Issues et Bugs** : Créer une issue dans le repository
2. **Questions techniques** : Consulter la documentation existante
3. **Améliorations** : Soumettre des pull requests
4. **Discussions** : Participer aux discussions techniques

---

## 🎯 Conclusion

Ce guide fournit une documentation complète pour utiliser l'écosystème ComfyUI-Qwen sécurisé. L'architecture est conçue pour être :

- ✅ **Sécurisée** : Authentification bcrypt avec tokens unifiés
- ✅ **Performante** : GPU optimisé avec modèles FP8
- ✅ **Maintenable** : Scripts consolidés et documentés
- ✅ **Scalable** : Architecture modulaire et extensible
- ✅ **Fiable** : Validation complète et monitoring intégré

### Prochaines Étapes

1. **Explorer les fonctionnalités** : Tester les différents workflows
2. **Personnaliser les modèles** : Ajouter des modèles personnalisés
3. **Intégrer avec vos applications** : Utiliser les clients API
4. **Contribuer à l'écosystème** : Améliorer les scripts et documentation

L'écosystème ComfyUI-Qwen est maintenant **Production Ready** et peut être utilisé pour des projets de génération d'images sécurisés et performants.

---

**Guide créé par** : Roo Code - Mode Documentation  
**Date de création** : 2025-11-25T01:00:00Z  
**Version** : 2.0.0 - Guide Complet d'Utilisation  
**Statut** : ✅ PRODUCTION READY