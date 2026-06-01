# 📚 Documentation GenAI CoursIA

Documentation de référence pour l'écosystème GenAI/Image CoursIA.

---

## 🎯 Vue d'Ensemble

Cette documentation technique couvre l'ensemble de l'infrastructure GenAI Images intégrée au projet CoursIA. L'écosystème est actuellement structuré en deux piliers principaux :

1.  **ComfyUI (Stable v1.0)** : Infrastructure de production stabilisée, sécurisée et documentée.
2.  **Forge (Chantier)** : Environnement expérimental pour SD XL Turbo, en cours de migration vers les standards d'infrastructure.

## 🏛️ Piliers de l'Infrastructure

### 1. ComfyUI - Environnement Stable v1.0 ✅

Le cœur de notre infrastructure de génération d'images, basé sur ComfyUI, a atteint sa maturité v1.0.

*   **État** : 🟢 Production Stable (Validé Phase 30)
*   **Référence Technique** : [**Configuration de Référence v1.0**](../suivis/genai-image/phase-32-restauration-post-reorganisation/CONFIGURATION_REFERENCE_V1.0_STABLE.md)
*   **Fonctionnalités Clés** :
    *   Authentification unifiée (Basic Auth + Token Sync)
    *   Support Qwen-VL et Flux.1
    *   **Nouveau (Phase 39)** : Support Z-Image Turbo (Lumina-Next) via Diffusers Wrapper
    *   Architecture Docker optimisée
    *   Monitoring et logs centralisés
    *   Scripts de gestion unifiés (`manage-genai.ps1`)

### 2. Forge - Environnement Expérimental 🚧

L'environnement Forge, dédié à la génération ultra-rapide (SD XL Turbo), est en cours de consolidation.

*   **État** : 🟠 Chantier en cours
*   **Objectif** : Dockerisation et intégration à l'infrastructure standardisée.
*   **Roadmap** :
    *   [ ] Dockerisation du service Forge
    *   [ ] Intégration de l'authentification unifiée
    *   [ ] Standardisation des notebooks associés

---

## 📖 Guides Utilisateur

| Document | Description | Public |
|----------|-------------|--------|
| [**Guide Utilisateur**](user-guide.md) | Guide complet pour utiliser l'écosystème GenAI Images | Utilisateurs, Étudiants |
| [**Guide Déploiement**](deployment-guide.md) | Procédures de déploiement en environnement de production | Administrateurs, DevOps |
| [**Guide Troubleshooting**](troubleshooting.md) | Résolution des problèmes courants | Support, Administrateurs |

## 🏗️ Architecture & Conception

| Document | Description | Public |
|----------|-------------|--------|
| [**Architecture Générale**](architecture.md) | Architecture complète de l'écosystème GenAI Images | Architectes, Développeurs |
| [**Standards Développement**](development-standards.md) | Standards et conventions de développement | Développeurs |
| [**Ecosystem README**](ecosystem-readme.md) | Vue d'ensemble de l'écosystème | Tous |

## 🐳 Infrastructure Docker

| Document | Description | Public |
|----------|-------------|--------|
| [**Spécifications Docker**](docker-specs.md) | Spécifications techniques des containers Docker | DevOps, Développeurs |
| [**Docker Orchestration**](docker-orchestration.md) | Orchestration et gestion des services Docker | DevOps |
| [**Docker Lifecycle Management**](docker-lifecycle-management.md) | Gestion du cycle de vie des containers | DevOps, Administrateurs |

## ⚙️ Configuration & Intégration

| Document | Description | Public |
|----------|-------------|--------|
| [**Configurations Environnement**](environment-configurations.md) | Configuration des environnements (dev, prod) | DevOps, Développeurs |
| [**Procédures Intégration**](integration-procedures.md) | Procédures d'intégration MCP | Développeurs Backend |
| [**Templates Phase 2**](phase2-templates.md) | Templates pour implémentation Phase 2 | Développeurs |
| [**Configuration Référence Qwen**](../suivis/genai-image/phase-32-restauration-post-reorganisation/CONFIGURATION_REFERENCE_V1.0_STABLE.md) | Configuration stable ComfyUI Qwen | DevOps, Architectes |

## 🧪 Tests & Scripts

| Document | Description | Public |
|----------|-------------|--------|
| [**Tests Infrastructure**](infrastructure-tests.md) | Suite de tests pour validation infrastructure | QA, DevOps |
| [**Scripts PowerShell**](powershell-scripts.md) | Scripts d'automatisation PowerShell | DevOps, Administrateurs |

> **Nouveau :** Utilisez le script unifié `scripts/genai-auth/manage-genai.ps1` pour toutes les opérations courantes (Déploiement, Diagnostic, Validation).

---

## 📓 État des Notebooks

### ✅ Notebooks Fonctionnels (ComfyUI)
Ces notebooks sont validés et opérationnels sur l'infrastructure stable v1.0.

*   `01-Images-Foundation/01-5-Qwen-Image-Edit.ipynb` : Édition d'images avec Qwen-VL et ComfyUI.
*   `00-GenAI-Environment/00-4-Environment-Validation.ipynb` : Validation de l'environnement.

### 🚧 Notebooks à Consolider (Forge)
Ces notebooks nécessitent une attention particulière en attendant la finalisation du chantier Forge.

*   `01-Images-Foundation/01-4-Forge-SD-XL-Turbo.ipynb` : Génération rapide avec SD XL Turbo (En attente de dockerisation Forge).

---

## 📋 Suivis de Mission

Les rapports de mission et suivis chronologiques du développement de l'infrastructure GenAI sont disponibles dans le répertoire dédié:

➡️ **[docs/suivis/genai-image/](docs/suivis/genai-image/)** - Rapports historiques et suivis de phases

### 🏆 Rapports Clés
*   ✅ **[Rapport Final Mission Qwen ComfyUI](../suivis/genai-image/RAPPORT-FINAL-MISSION-QWEN-COMFYUI.md)** : Synthèse complète de la stabilisation de l'environnement.
*   🔒 **[Configuration de Référence](../suivis/genai-image/phase-32-restauration-post-reorganisation/CONFIGURATION_REFERENCE_V1.0_STABLE.md)** : Source de vérité technique pour la reconstruction.

---

## 🚀 Démarrage Rapide

### Pour les Utilisateurs

1. Consultez le [**Guide Utilisateur**](user-guide.md)
2. Suivez les instructions de configuration de l'environnement
3. Explorez les notebooks dans `MyIA.AI.Notebooks/GenAI/`

### Pour les Administrateurs

1. Lisez l'[**Architecture Générale**](architecture.md)
2. Suivez le [**Guide Déploiement**](deployment-guide.md)
3. Configurez l'environnement selon [**Configurations Environnement**](environment-configurations.md)

### Pour les Développeurs

1. Familiarisez-vous avec les [**Standards Développement**](development-standards.md)
2. Consultez les [**Templates Phase 2**](phase2-templates.md)
3. Référez-vous aux [**Procédures Intégration**](integration-procedures.md)

---

## 🔗 Ressources Externes

- **Notebooks GenAI**: `MyIA.AI.Notebooks/GenAI/`
- **Scripts d'automatisation**: `scripts/`
- **Configuration Docker**: `docker-compose.yml`

---

## 📝 Maintenance

**Méthode**: SDDD (Semantic-Documentation-Driven-Design)
**Dernière mise à jour**: 10 décembre 2025
**Responsable**: Équipe CoursIA GenAI

---

*📚 Documentation organisée pour une navigation optimale et une synchronisation efficace entre agents*