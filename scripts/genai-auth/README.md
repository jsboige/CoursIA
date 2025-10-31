# Scripts GenAI Auth - Structure Consolidée

Ce répertoire contient les scripts consolidés et paramétriques pour la gestion de l'authentification et de la configuration des services GenAI (ComfyUI, Qwen, etc.).

## 📁 Scripts Principaux

### 🔐 Gestionnaire d'Authentification
- **`genai-auth-manager.py`** - Gestionnaire principal d'authentification GenAI
  - Génération de tokens Bearer sécurisés
  - Configuration multi-services (ComfyUI Qwen, Forge, etc.)
  - Validation des tokens existants
  - Diagnostic des problèmes d'authentification
  - Gestion des environnements d'authentification

  ```bash
  # Génération de tokens pour ComfyUI Qwen
  python genai-auth-manager.py generate --service comfyui-qwen
  
  # Validation des tokens ComfyUI Qwen
  python genai-auth-manager.py validate --service comfyui-qwen
  
  # Diagnostic des problèmes d'authentification
  python genai-auth-manager.py diagnose --service comfyui-qwen
  
  # Liste des services configurés
  python genai-auth-manager.py list-services
  
  # Affichage de la configuration
  python genai-auth-manager.py show-config
  ```

### 🐳 Gestionnaire Docker Qwen
- **`docker-qwen-manager.py`** - Gestionnaire Docker pour ComfyUI Qwen
  - Démarrage/arrêt/redémarrage des conteneurs
  - Monitoring des ressources (CPU, mémoire, disque, réseau)
  - Validation des configurations Docker
  - Gestion des volumes et réseaux
  - Diagnostic des problèmes Docker

  ```bash
  # Démarrer le conteneur ComfyUI Qwen
  python docker-qwen-manager.py start --container comfyui-qwen
  
  # Arrêter le conteneur ComfyUI Qwen
  python docker-qwen-manager.py stop --container comfyui-qwen
  
  # Redémarrer le conteneur ComfyUI Qwen
  python docker-qwen-manager.py restart --container comfyui-qwen
  
  # Vérifier le statut d'un conteneur
  python docker-qwen-manager.py status --container comfyui-qwen
  
  # Vérifier la santé d'un conteneur
  python docker-qwen-manager.py health --container comfyui-qwen
  
  # Monitorer les ressources d'un conteneur
  python docker-qwen-manager.py monitor --container comfyui-qwen --duration 300
  
  # Valider la configuration Docker complète
  python docker-qwen-manager.py validate-setup
  
  # Afficher la configuration Docker actuelle
  python docker-qwen-manager.py show-config
  ```

### 🔍 Validateur Complet Qwen
- **`qwen-validator.py`** - Validateur complet pour la solution Qwen ComfyUI
  - Validation complète de l'environnement
  - Tests de connectivité et d'API
  - Validation des workflows JSON
  - Diagnostic des problèmes
  - Génération de rapports détaillés

  ```bash
  # Validation rapide
  python qwen-validator.py --mode quick
  
  # Validation complète
  python qwen-validator.py --mode comprehensive
  
  # Validation d'un workflow spécifique
  python qwen-validator.py --workflow workflow.json --output validation_report.json
  
  # Afficher la configuration
  python qwen-validator.py --show-config
  ```

### 🛠️ Setup Initial ComfyUI Qwen
- **`qwen-setup.py`** - Script de setup initial pour ComfyUI Qwen
  - Vérification des prérequis système
  - Installation des dépendances Python
  - Configuration de l'environnement
  - Configuration de l'authentification
  - Validation du setup complet

  ```bash
  # Setup complet
  python qwen-setup.py --full-setup
  
  # Vérification des prérequis seulement
  python qwen-setup.py --check-prereqs
  
  # Configuration de l'environnement seulement
  python qwen-setup.py --setup-env
  
  # Installation des dépendances seulement
  python qwen-setup.py --install-deps
  
  # Configuration de l'authentification seulement
  python qwen-setup.py --setup-auth
  
  # Afficher la configuration actuelle
  python qwen-setup.py --show-config
  ```

## 📊 Scripts Utilitaires Consolidés

Les scripts suivants sont conservés comme utilitaires spécialisés :

### Client Helper ComfyUI
- **`comfyui_client_helper.py`** - Client HTTP complet pour ComfyUI (1305 lignes)
  - Interface client/batch/investigation/debug
  - Gestionnaire de workflows
  - Système de plugins extensible

### Utilitaires de Workflow
- **`workflow_utils.py`** - Utilitaire consolidé pour la manipulation de workflows (489 lignes)
  - Validation JSON, correction des liens, optimisation
  - Backup et restauration de workflows

### Diagnostic Complet
- **`diagnostic_utils.py`** - Utilitaire consolidé pour le diagnostic (426 lignes)
  - Diagnostic environnement Python, Docker, services
  - Génération de rapports détaillés

## 🗂️ Scripts Supprimés

Les scripts suivants ont été consolidés dans les nouveaux scripts paramétriques et supprimés du répertoire :

### Scripts d'Authentification
- `generate-bearer-tokens.py` → Consolidé dans `genai-auth-manager.py`
- `debug_auth_token.py` → Consolidé dans `genai-auth-manager.py`
- `extract-bearer-tokens.ps1` → Consolidé dans `genai-auth-manager.py`

### Scripts de Configuration Docker
- `configure-comfyui-auth.ps1` → Consolidé dans `docker-qwen-manager.py`
- `validate-docker-config.ps1` → Consolidé dans `docker-qwen-manager.py`
- `check-docker-containers.ps1` → Consolidé dans `docker-qwen-manager.py`
- `create-venv-in-container.sh` → Consolidé dans `qwen-setup.py`
- `recreate-venv-in-container.sh` → Consolidé dans `qwen-setup.py`

### Scripts de Validation
- `validate-qwen-solution.py` → Consolidé dans `qwen-validator.py`
- `test_qwen_workflow_validation.py` → Consolidé dans `qwen-validator.py`
- `test_qwen_workflow_final.py` → Consolidé dans `qwen-validator.py`
- `test_qwen_simple.py` → Consolidé dans `qwen-validator.py`
- `test_submit_workflow.py` → Consolidé dans `qwen-validator.py`
- `diagnostic-qwen-complete.py` → Consolidé dans `diagnostic_utils.py`

### Scripts de Réparation
- `fix_workflow_links.py` → Consolidé dans `workflow_utils.py`
- `fix-qwen-workflow.py` → Consolidé dans `qwen-validator.py`
- `fix-comfyui-dependencies.sh` → Consolidé dans `qwen-setup.py`

### Scripts de Setup
- `init-venv.sh` → Consolidé dans `qwen-setup.py`
- `install-missing-dependencies.sh` → Consolidé dans `qwen-setup.py`
- `setup-and-test-comfyui.sh` → Consolidé dans `qwen-setup.py`

### Scripts d'Exploration
- `explore-qwen-custom-node.ps1` → Consolidé dans `comfyui_client_helper.py`

## 📋 Fichiers de Données

- `validation_complete_qwen_system_20251030_234336.json` - Données de validation système
- `validation_complete_qwen_system.py` - Script de validation système (conservé)

## 🔧 Configuration

Les scripts utilisent des fichiers de configuration JSON pour la persistance des paramètres :

- `genai_auth_config.json` - Configuration du gestionnaire d'authentification
- `docker_qwen_config.json` - Configuration du gestionnaire Docker Qwen
- `qwen_validator_config.json` - Configuration du validateur Qwen
- `qwen_setup_config.json` - Configuration du setup Qwen

## 🚀 Avantages de la Consolidation

### ✅ Maintenance Simplifiée
- **4 scripts principaux** au lieu de 28 scripts spécialisés
- **Configuration centralisée** dans des fichiers JSON
- **Paramétrisation complète** avec arguments flexibles
- **Logging structuré** pour tous les scripts
- **Gestion d'erreurs** robuste et cohérente

### 🎯 Fonctionnalités Améliorées
- **Gestion multi-services** dans le gestionnaire d'authentification
- **Monitoring avancé** avec échantillonnage des ressources
- **Validation modulaire** avec modes rapide/complet/workflow
- **Setup automatisé** avec validation des prérequis
- **Extensibilité** via système de plugins (client helper)
- **Rapports détaillés** au format JSON avec métadonnées

### 📈 Utilisation Recommandée

1. **Utiliser les scripts principaux** pour les opérations courantes
2. **Réserver les scripts spécialisés** pour les cas d'usage avancé
3. **Configurer les scripts** via les fichiers de configuration JSON
4. **Consulter les logs** pour le diagnostic des problèmes

## 🔒 Sécurité

- Les tokens sont générés avec bcrypt (work factor 12)
- Les configurations sont sauvegardées dans des fichiers JSON
- Les scripts incluent une validation des arguments et des erreurs détaillées
- Les opérations sensibles nécessitent une confirmation explicite

---

*Dernière mise à jour : 2025-10-31*