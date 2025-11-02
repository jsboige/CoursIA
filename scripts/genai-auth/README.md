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

## 🆕 Scripts Phase 29 - ComfyUI-Login & Custom Nodes Qwen

Les scripts suivants ont été créés dans la Phase 29 pour gérer l'authentification ComfyUI-Login et l'installation des custom nodes Qwen :

### 🔧 Installation Custom Nodes Qwen
- **`qwen-custom-nodes-installer.py`** ⭐ **NOUVEAU** - Script consolidé d'installation complète des custom nodes Qwen
  - Suppression installation existante (réinstallation propre)
  - Clonage repository `gokayfem/ComfyUI-QwenImageWanBridge`
  - Installation dépendances Python (requirements.txt)
  - Vérification/Installation ComfyUI-Login
  - Synchronisation credentials Windows → WSL
  - Redémarrage container Docker
  - Validation des 28 custom nodes chargés
  - Génération rapport SDDD numéroté 22
  
  ```bash
  # Installation complète (attendre validation utilisateur avant exécution)
  python scripts/genai-auth/qwen-custom-nodes-installer.py
  
  # Vérification des dépendances avant installation
  python docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/transient-scripts/07-verify-installer-dependencies-20251102-013546.py
  ```
  
  **Contexte** : Suite au diagnostic Phase 29 révélant que seulement 4/28 custom nodes Qwen étaient chargés (14.3%), ce script réinstalle proprement l'ensemble du système custom nodes basé sur l'archéologie documentaire du Rapport 21 (Phase 12C).
  
  **Livrables** :
  - Script consolidé dans `scripts/genai-auth/`
  - Rapport automatique numéroté 22 dans `docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/`
  - Validation 28/28 custom nodes chargés
  
  **Référence documentaire** : [Rapport 21 - Archéologie Installation Qwen](../../docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/21-RAPPORT-FINAL-ARCHEOLOGIE-INSTALLATION-QWEN-20251102-014600.md)

### Installation et Configuration ComfyUI-Login
- **`install-comfyui-login.py`** ⭐ - Script consolidé d'installation et configuration ComfyUI-Login
  - Vérification installation existante (WSL)
  - Clonage automatique du repository GitHub
  - Installation des dépendances Python (bcrypt)
  - Synchronisation des credentials depuis `.secrets/`
  - Redémarrage container Docker (optionnel)
  - Test de validation de l'authentification
  
  ```bash
  # Installation complète avec redémarrage
  python install-comfyui-login.py
  
  # Installation sans redémarrage (pour tests)
  python install-comfyui-login.py --skip-restart
  
  # Avec chemin workspace custom
  python install-comfyui-login.py \
    --workspace /custom/path/comfyui-qwen \
    --secrets .secrets/custom-token.token
  ```

### Tests d'Authentification
- **`test-comfyui-auth-simple.py`** - Test rapide d'authentification ComfyUI-Login
  - Test de connectivité avec hash bcrypt
  - Affichage des informations système
  - Diagnostic clair (HTTP 200/401)
  
  ```bash
  python test-comfyui-auth-simple.py
  ```

### Tests de Génération d'Images
- **`test-comfyui-image-simple.py`** - Test de génération d'image avec authentification
  - Soumission workflow minimal
  - Suivi de l'exécution avec timeout
  - Validation de la génération d'image
  
  ```bash
  python test-comfyui-image-simple.py
  ```

### ⚠️ Important - Découverte Critique

**ComfyUI-Login utilise une implémentation inhabituelle** :
- Le serveur attend le **HASH BCRYPT LUI-MÊME** comme Bearer token
- Ce n'est PAS le texte brut du mot de passe qui est envoyé
- Cette découverte est documentée dans le [Rapport 18](../../docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/18-resolution-finale-authentification-comfyui-login-20251101-232000.md)

**Exemple de token correct** :
```bash
curl -X GET \
  -H "Authorization: Bearer $2b$12$2jPJrb7dmsM7fw0..PoEqu8nmGarw0vnYYdGw5BFmcZ52bGfwf5M2" \
  http://localhost:8188/system_stats
```

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

## 📋 Consolidation Finale - Phase 29

### Décision Architecturale : Scripts Standalone vs. Intégration

Suite à l'analyse approfondie des scripts consolidés existants (`genai_auth_manager.py` - 2500+ lignes, `validation_complete_qwen_system.py` - 1800+ lignes, `workflow_utils.py` - 489 lignes), la décision a été prise de **conserver les 3 nouveaux scripts Phase 29 comme solutions standalone définitives** plutôt que de les intégrer.

**Rationale de cette décision** :
- ✅ **Stabilité** : Évite le risque de régression dans des scripts critiques et complexes
- ✅ **Maintenabilité** : Les nouveaux scripts sont autonomes, simples, et bien documentés
- ✅ **SDDD Compliance** : Approche documentaire privilégiée sur la refactorisation massive
- ✅ **Testabilité** : Scripts standalone plus faciles à tester et valider isolément
- ✅ **Scope défini** : Chaque script a une responsabilité unique et claire

### Scripts Phase 29 - Solution Définitive

Les 3 scripts suivants constituent la **solution finale officielle** pour la gestion de ComfyUI-Login :

1. **`install-comfyui-login.py`** (197 lignes)
   - Installation automatisée complète du custom node ComfyUI-Login
   - Synchronisation des credentials bcrypt depuis `.secrets/`
   - Validation post-installation avec test d'authentification
   - **Usage** : À exécuter une seule fois lors du setup initial ou après rebuild du container

2. **`test-comfyui-auth-simple.py`** (79 lignes)
   - Test rapide d'authentification (< 5 secondes)
   - Diagnostic clair du statut (HTTP 200/401)
   - **Usage** : Validation quotidienne de l'authentification

3. **`test-comfyui-image-simple.py`** (170 lignes)
   - Test end-to-end de génération d'image
   - Workflow minimal avec timeout configurable
   - Validation de la présence de l'image générée
   - **Usage** : Test de non-régression après modifications système

### Script Transient Final

- **`14-test-generation-images-final-20251102-005300.py`** (Script transient de validation finale)
  - Localisation : `docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/transient-scripts/`
  - Test complet end-to-end du système Qwen
  - Validation Docker + Authentification + Génération
  - Rapport JSON détaillé de validation

### Documentation Phase 29

Pour la documentation complète de la Phase 29, consulter :

- **Rapport Final** : [`19-rapport-final-phase-29-resolution-complete-20251102-005300.md`](../../docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/19-rapport-final-phase-29-resolution-complete-20251102-005300.md)
  - Chronologie complète (31 oct - 2 nov 2025)
  - Synthèse des 14 scripts transients créés
  - Découverte critique sur l'authentification bcrypt
  - 18 rapports intermédiaires référencés

- **Rapport Archéologie** : [`17-archeologie-authentification-comfyui-SDDD-20251101-235600.md`](../../docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/17-archeologie-authentification-comfyui-SDDD-20251101-235600.md)
  - Méthodologie d'investigation documentaire
  - Analyse des 15+ rapports précédents

- **Rapport Résolution** : [`18-resolution-finale-authentification-comfyui-login-20251101-232000.md`](../../docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/18-resolution-finale-authentification-comfyui-login-20251101-232000.md)
  - Découverte du mécanisme bcrypt hash comme bearer token
  - Solution technique complète

### Prochaines Étapes

Les scripts Phase 29 sont maintenant la **référence officielle** pour :
- Installation de ComfyUI-Login dans le container Docker
- Tests d'authentification API
- Validation de génération d'images

Pour les évolutions futures, privilégier :
1. **Extension** : Créer de nouveaux scripts standalone plutôt que modifier les existants
2. **Documentation** : Mettre à jour ce README et créer des rapports SDDD
3. **Tests** : Utiliser les scripts Phase 29 comme template pour de nouveaux tests

---

*Dernière mise à jour : 2025-11-02 - Phase 29 - Consolidation finale et scripts standalone définitifs*
*Dernière mise à jour : 2025-11-01 - Phase 29 - Ajout scripts ComfyUI-Login*