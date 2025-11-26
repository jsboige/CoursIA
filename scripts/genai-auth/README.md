# Scripts GenAI Auth - Structure Consolidée Phase 29

Ce répertoire contient les scripts consolidés et paramétriques pour la gestion de l'authentification et de la configuration des services GenAI (ComfyUI, Qwen, etc.).

## 📁 Structure du Répertoire

```
scripts/genai-auth/
├── README.md                          (ce fichier)
├── core/                              Scripts principaux et validation
│   ├── validate_genai_ecosystem.py     Validation complète écosystème
│   ├── diagnose_comfyui_auth.py        Diagnostic authentification ComfyUI
│   ├── install_comfyui_login.py       Installation ComfyUI-Login
│   └── setup_complete_qwen.py         Wrapper d'installation complète Qwen
├── utils/                             Utilitaires et helpers
│   ├── benchmark.py                    Benchmark de performance
│   ├── comfyui_client_helper.py       Client HTTP complet pour ComfyUI
│   ├── diagnostic_utils.py            Utilitaires de diagnostic
│   ├── docker_qwen_manager.py         Gestionnaire Docker Qwen
│   ├── genai_auth_manager.py          Gestionnaire d'authentification
│   └── workflow_utils.py              Utilitaires de manipulation de workflows
├── tests/                             Scripts de test
│   └── genai-improvements/           Tests et débogage
├── workflows/                         Scripts de workflows validés
├── archive/                           Scripts archivés
│   ├── scripts_epars/                  Scripts obsolètes consolidés
│   └── archive-wsl/                   Scripts WSL archivés
└── backup_consolidation/              Backups automatiques
```

## 🚀 Scripts Principaux

### 🔐 Scripts Principaux et Validation (core/)

#### `validate_genai_ecosystem.py` ⭐ NOUVEAU
Script de validation complète de l'écosystème GenAI Images.

**Fonctionnalités** :
- Validation structure fichiers et notebooks
- Vérification configuration (.env, clés API)
- Tests connectivité APIs (OpenAI, OpenRouter)
- Validation authentification ComfyUI (web et API)
- Contrôle qualité notebooks (BOM, JSON valide)
- Génération rapport JSON détaillé

**Usage** :
```bash
# Validation complète
python scripts/genai-auth/core/validate_genai_ecosystem.py

# Mode verbeux avec corrections automatiques
python scripts/genai-auth/core/validate_genai_ecosystem.py --verbose --fix

# Génération rapport JSON
python scripts/genai-auth/core/validate_genai_ecosystem.py --report
```

#### `diagnose_comfyui_auth.py` ⭐ NOUVEAU
Script de diagnostic complet pour l'authentification ComfyUI.

**Fonctionnalités** :
- Diagnostic statut conteneur ComfyUI
- Test connectivité service
- Validation configuration authentification
- Analyse logs erreurs
- Génération rapport diagnostic

**Usage** :
```bash
# Diagnostic complet
python scripts/genai-auth/core/diagnose_comfyui_auth.py

# Diagnostic avec mode verbeux
python scripts/genai-auth/core/diagnose_comfyui_auth.py --verbose
```

#### `install_comfyui_login.py` ⭐
Script consolidé d'installation et configuration ComfyUI-Login.

**Fonctionnalités** :
- Vérification installation existante (WSL)
- Clonage automatique du repository GitHub
- Installation des dépendances Python (bcrypt)
- Synchronisation des credentials depuis `.secrets/`
- Redémarrage container Docker (optionnel)
- Test de validation de l'authentification

**Usage** :
```bash
# Installation complète avec redémarrage
python scripts/genai-auth/core/install_comfyui_login.py

# Installation sans redémarrage (pour tests)
python scripts/genai-auth/core/install_comfyui_login.py --skip-restart

# Avec chemin workspace custom
python scripts/genai-auth/core/install_comfyui_login.py \
  --workspace /custom/path/comfyui-qwen \
  --secrets .secrets/custom-token.token
```

#### `setup_complete_qwen.py` ⭐ NEW - Wrapper d'Installation Automatisée
Script consolidé d'installation complète du système Qwen (Phase 29).

**Fonctionnalités** :
- Vérification prérequis (Docker, Python, huggingface-cli)
- Démarrage container Docker comfyui-qwen
- Installation ComfyUI-Login (appelle `install_comfyui_login.py`)
- Téléchargement modèles FP8 officiels Comfy-Org (29GB)
- Configuration authentification bcrypt
- Test génération d'image end-to-end
- Génération rapport JSON automatique

**Usage** :
```bash
# Installation complète (tous les composants)
python scripts/genai-auth/core/setup_complete_qwen.py

# Installation sans téléchargement modèles (déjà présents)
python scripts/genai-auth/core/setup_complete_qwen.py --skip-models

# Installation sans test de génération d'image
python scripts/genai-auth/core/setup_complete_qwen.py --skip-test

# Installation minimale (prérequis + auth + config uniquement)
python scripts/genai-auth/core/setup_complete_qwen.py \
  --skip-docker \
  --skip-models \
  --skip-test

# Installation avec répertoire de rapport custom
python scripts/genai-auth/core/setup_complete_qwen.py \
  --report-dir ./rapports/phase-29
```

**Options disponibles** :
- `--skip-docker` : Ne pas démarrer le container Docker
- `--skip-models` : Ne pas télécharger les modèles FP8
- `--skip-auth` : Ne pas installer ComfyUI-Login
- `--skip-test` : Ne pas exécuter le test de génération d'image
- `--report-dir PATH` : Répertoire de génération du rapport (défaut: `rapports/`)

**Rapport JSON généré** :
```json
{
  "timestamp_start": "2025-11-02T15:45:39.215595",
  "timestamp_end": "2025-11-02T15:46:12.345678",
  "status": "SUCCESS",
  "steps": [
    {"name": "Vérification prérequis", "status": "SUCCESS", "timestamp": "..."},
    {"name": "Démarrage container Docker", "status": "SKIPPED", "timestamp": "..."},
    {"name": "Installation ComfyUI-Login", "status": "SUCCESS", "timestamp": "..."},
    {"name": "Téléchargement modèles FP8", "status": "SKIPPED", "timestamp": "..."},
    {"name": "Configuration authentification", "status": "SUCCESS", "timestamp": "..."},
    {"name": "Test génération image", "status": "SUCCESS", "timestamp": "..."}
  ],
  "errors": []
}
```

**Modèles FP8 installés** :
- **Diffusion** : `qwen_image_edit_2509_fp8_e4m3fn.safetensors` (20GB)
- **CLIP** : `qwen_2.5_vl_7b_fp8_scaled.safetensors` (8.8GB)
- **VAE** : `qwen_image_vae.safetensors` (243MB)

**Prérequis** :

### Installation Automatique
Le script `setup_complete_qwen.py` installera automatiquement :
- ✅ `huggingface-hub` (si absent, installation automatique via pip)

### Installation Manuelle Requise
Vous devez installer manuellement :
- Docker Desktop (avec WSL2)
- Python 3.8+
- Token HuggingFace dans `.secrets/.env.huggingface`

### 🔧 Utilitaires (utils/)

#### `benchmark.py` ⭐ NOUVEAU
Script de benchmark pour ComfyUI Qwen avec monitoring GPU.

**Fonctionnalités** :
- Mesure temps de génération d'images
- Monitoring utilisation GPU (mémoire, température, utilisation)
- Support authentification ComfyUI
- Génération rapport de performance
- Mode sans authentification disponible

**Usage** :
```bash
# Benchmark avec authentification
python scripts/genai-auth/utils/benchmark.py

# Benchmark sans authentification
python scripts/genai-auth/utils/benchmark.py --no-auth

# Benchmark avec workflow custom
python scripts/genai-auth/utils/benchmark.py --workflow custom_workflow.json
```

#### `test_comfyui_auth_simple.py`
Test rapide d'authentification ComfyUI-Login (< 5 secondes).

**Fonctionnalités** :
- Test de connectivité avec hash bcrypt
- Affichage des informations système
- Diagnostic clair (HTTP 200/401)

**Usage** :
```bash
python scripts/genai-auth/utils/test_comfyui_auth_simple.py
```

**Résultat attendu** :
```
✅ SUCCÈS - Authentification réussie!
📊 Informations Système:
   • OS: Linux
   • RAM Totale: 31.26 GB
   • ComfyUI Version: v0.2.7
```

#### `comfyui_client_helper.py`
Client HTTP complet pour ComfyUI (1305 lignes).

**Fonctionnalités** :
- Interface client/batch/investigation/debug
- Gestionnaire de workflows
- Système de plugins extensible

#### `workflow_utils.py`
Utilitaire consolidé pour la manipulation de workflows (489 lignes).

**Fonctionnalités** :
- Validation JSON, correction des liens, optimisation
- Backup et restauration de workflows

#### `diagnostic_utils.py`
Utilitaire consolidé pour le diagnostic (426 lignes).

**Fonctionnalités** :
- Diagnostic environnement Python, Docker, services
- Génération de rapports détaillés

#### `genai_auth_manager.py`
Gestionnaire principal d'authentification GenAI.

**Fonctionnalités** :
- Génération de tokens Bearer sécurisés
- Configuration multi-services (ComfyUI Qwen, Forge, etc.)
- Validation des tokens existants
- Diagnostic des problèmes d'authentification

**Usage** :
```bash
# Génération de tokens pour ComfyUI Qwen
python scripts/genai-auth/utils/genai_auth_manager.py generate --service comfyui-qwen

# Validation des tokens ComfyUI Qwen
python scripts/genai-auth/utils/genai_auth_manager.py validate --service comfyui-qwen

# Diagnostic des problèmes d'authentification
python scripts/genai-auth/utils/genai_auth_manager.py diagnose --service comfyui-qwen
```

#### `docker_qwen_manager.py`
Gestionnaire Docker pour ComfyUI Qwen.

**Fonctionnalités** :
- Démarrage/arrêt/redémarrage des conteneurs
- Monitoring des ressources (CPU, mémoire, disque, réseau)
- Validation des configurations Docker

**Usage** :
```bash
# Démarrer le conteneur ComfyUI Qwen
python scripts/genai-auth/utils/docker_qwen_manager.py start --container comfyui-qwen

# Vérifier le statut d'un conteneur
python scripts/genai-auth/utils/docker_qwen_manager.py status --container comfyui-qwen

# Monitorer les ressources d'un conteneur
python scripts/genai-auth/utils/docker_qwen_manager.py monitor --container comfyui-qwen --duration 300
```

## ⚠️ Découverte Critique - Authentification ComfyUI-Login

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

## 📦 Scripts Archivés (Phase 29)

Les scripts transients de la Phase 29 ont été archivés dans :
`docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/scripts-archives/`

**Scripts archivés** :
- `test_comfyui_image_simple.py` - Remplacé par le test end-to-end du wrapper
- `test-comfyui-image-qwen-correct.py` - Script de test spécifique à une phase de débogage
- `qwen-custom-nodes-installer.py` - Installation des custom nodes Qwen (non requise pour le workflow de base)
- `list-qwen-nodes.py` - Script de diagnostic devenu obsolète
- `resync-credentials-complete.py` - Synchronisation gérée par `install_comfyui_login.py`

## 🗑️ Scripts Supprimés

Les scripts suivants ont été supprimés car remplacés par les nouveaux scripts consolidés :
- `qwen-setup.py` - Remplacé par le wrapper `setup_complete_qwen.py` (à venir)
- `qwen-validator.py` - Remplacé par les étapes de validation du wrapper
- `validation_complete_qwen_system.py` - Remplacé par le nouveau wrapper
- `genai_auth_manager.py` - Doublon de `genai_auth_manager.py`

## 📋 Architecture Finale Validée (Phase 29)

La solution fonctionnelle repose sur :
- **Modèles FP8 Officiels de Comfy-Org** : Architecture séparée en 3 composants (UNET, CLIP, VAE)
- **Workflow 100% Natif ComfyUI** : Le workflow de génération d'image validé n'utilise **aucun custom node Qwen**
- **Authentification via ComfyUI-Login** : Custom node spécifique pour la gestion de l'authentification

### Workflow de Génération d'Image Validé

Nodes natifs utilisés :
- `UNETLoader`
- `CLIPLoader`
- `VAELoader`
- `EmptySD3LatentImage`
- `CLIPTextEncode`
- `KSampler`
- `VAEDecode`

Documentation complète dans [`RAPPORT-FINAL-PHASE-29-20251102.md`](../../docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/RAPPORT-FINAL-PHASE-29-20251102.md).

## 🔒 Sécurité

- Les tokens sont générés avec bcrypt (work factor 12)
- Les credentials sont stockés dans `.secrets/` (gitignore)
- Les scripts incluent une validation des arguments et des erreurs détaillées
- Les opérations sensibles nécessitent une confirmation explicite

## 📚 Documentation Phase 29

Pour la documentation complète de la Phase 29, consulter :

- **Rapport Final** : [`RAPPORT-FINAL-PHASE-29-20251102.md`](../../docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/RAPPORT-FINAL-PHASE-29-20251102.md)
  - Chronologie complète (31 oct - 2 nov 2025)
  - Synthèse des 31 rapports de la phase
  - Découverte critique sur l'authentification bcrypt

- **Plan de Consolidation** : [`PLAN-CONSOLIDATION-FINALE-PHASE-29.md`](../../docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/PLAN-CONSOLIDATION-FINALE-PHASE-29.md)
  - Catégorisation détaillée des scripts
  - Architecture cible consolidée
  - Plan d'exécution des sous-tâches

## 🚀 Prochaines Étapes

Les scripts Phase 29 sont maintenant la **référence officielle** pour :
- Installation de ComfyUI-Login dans le container Docker
- Tests d'authentification API
- Validation de génération d'images

Pour les évolutions futures, privilégier :
1. **Extension** : Créer de nouveaux scripts standalone plutôt que modifier les existants
2. **Documentation** : Mettre à jour ce README et créer des rapports SDDD
3. **Tests** : Utiliser les scripts Phase 29 comme template pour de nouveaux tests

---

*Dernière mise à jour : 2025-11-02 15:20:00 - Phase 29 - Nettoyage et réorganisation selon plan de consolidation*