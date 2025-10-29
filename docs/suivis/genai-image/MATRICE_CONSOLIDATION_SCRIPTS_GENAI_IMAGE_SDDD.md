# 📊 Matrice de Consolidation Scripts GenAI-Image - SDDD

**Date** : 2025-10-29  
**Mission** : Consolidation des scripts des phases passées et finalisation de la restauration Qwen  
**Méthodologie** : SDDD (Semantic Driven Development & Documentation)

---

## 🎯 Objectif de Consolidation

Réduire les 16 scripts historiques dispersés en **4 scripts consolidés** optimisés selon le modèle éprouvé `genai-auth` :

1. `setup-docker-compose.ps1` - Configuration Docker unifiée
2. `diagnostic-genai-image.py` - Diagnostic complet GenAI-Image  
3. `configure-qwen-setup.py` - Configuration Qwen unifiée
4. `deploy-genai-image.py` - Déploiement unifié

---

## 📋 Matrice de Mapping Scripts → Cibles

### 🐳 Scripts Docker/Container (5 scripts → 1 script)

| Script Source | Phase | Fonctionnalité | Scripts cibles | Priorité |
|--------------|--------|----------------|----------------|-----------|
| `01-setup-docker-compose.ps1` | phase-01 | Setup Docker Compose initial | `setup-docker-compose.ps1` | **CRITIQUE** |
| `01-configure-sd3-paths.ps1` | phase-03 | Configuration chemins SD3 | `setup-docker-compose.ps1` | **HAUTE** |
| `01-configure-sdxl-paths.ps1` | phase-04 | Configuration chemins SDXL | `setup-docker-compose.ps1` | **HAUTE** |
| `01-install-comfyui-manager.ps1` | phase-08 | Installation ComfyUI Manager | `setup-docker-compose.ps1` | **MOYENNE** |
| `01-update-docker-compose-v2.ps1` | phase-20 | Mise à jour Docker Compose v2 | `setup-docker-compose.ps1` | **HAUTE** |

**Fonctionnalités à consolider** :
- Configuration multi-environnements (SD3, SDXL, ComfyUI)
- Gestion des volumes et réseaux Docker
- Validation des configurations post-déploiement
- Support ComfyUI Manager integration

---

### 🔍 Scripts Diagnostic/Validation (6 scripts → 1 script)

| Script Source | Phase | Fonctionnalité | Scripts cibles | Priorité |
|--------------|--------|----------------|----------------|-----------|
| `02-verify-models-download.ps1` | phase-01 | Vérification téléchargements modèles | `diagnostic-genai-image.py` | **CRITIQUE** |
| `01-launch-comfyui.ps1` | phase-02 | Lancement ComfyUI | `diagnostic-genai-image.py` | **CRITIQUE** |
| `02-check-comfyui-api.py` | phase-02 | Vérification API ComfyUI | `diagnostic-genai-image.py` | **CRITIQUE** |
| `01-run-qwen-t2i-test.py` | phase-10 | Test Qwen T2I | `diagnostic-genai-image.py` | **HAUTE** |
| `01-validate-qwen-t2i-output.py` | phase-12 | Validation sorties Qwen | `diagnostic-genai-image.py` | **HAUTE** |
| `01-cleanup-old-logs.ps1` | phase-21 | Nettoyage logs anciens | `diagnostic-genai-image.py` | **MOYENNE** |

**Fonctionnalités à consolider** :
- Vérification complète de l'environnement GenAI-Image
- Tests automatisés des APIs ComfyUI
- Validation des workflows Qwen (T2I, I2V, VLL)
- Diagnostic des performances et ressources
- Nettoyage et maintenance des logs

---

### ⚙️ Scripts Configuration Qwen (3 scripts → 1 script)

| Script Source | Phase | Fonctionnalité | Scripts cibles | Priorité |
|--------------|--------|----------------|----------------|-----------|
| `01-download-qwen-model.ps1` | phase-09 | Téléchargement modèle Qwen | `configure-qwen-setup.py` | **CRITIQUE** |
| `02-install-qwen-custom-node.ps1` | phase-09 | Installation nœud personnalisé Qwen | `configure-qwen-setup.py` | **CRITIQUE** |
| `01-fix-qwen-model-path.ps1` | phase-11 | Correction chemins modèle Qwen | `configure-qwen-setup.py` | **HAUTE** |

**Fonctionnalités à consolider** :
- Téléchargement automatique des modèles Qwen
- Installation et configuration des nœuds personnalisés
- Validation des chemins et permissions
- Configuration des paramètres Qwen (résolution, batch size, etc.)
- Intégration ComfyUI-QwenImageWanBridge

---

### 🚀 Scripts Déploiement/Setup (2 scripts → 1 script)

| Script Source | Phase | Fonctionnalité | Scripts cibles | Priorité |
|--------------|--------|----------------|----------------|-----------|
| `01-install-comfyui-manager.ps1` | phase-08 | Installation ComfyUI Manager | `deploy-genai-image.py` | **HAUTE** |
| `01-cleanup-old-logs.ps1` | phase-21 | Nettoyage logs anciens | `deploy-genai-image.py` | **MOYENNE** |

**Fonctionnalités à consolider** :
- Déploiement en environnement de production
- Configuration des services et monitoring
- Gestion des cycles de vie des applications
- Nettoyage automatisé des ressources temporaires

---

## 🔄 Analyse des Doublons

**Doublons identifiés avec scripts genai-auth existants** :
- ✅ **AUCUN DOUBLON DIRECT** 
- Les scripts genai-image sont complémentaires aux scripts genai-auth déjà consolidés
- **Synergie possible** : Intégration des workflows genai-image dans les scripts genai-auth existants

**Scripts genai-auth de référence** :
- `diagnostic-qwen-complete.py` → Peut être étendu pour GenAI-Image
- `validate-qwen-solution.py` → Peut valider tous les workflows GenAI-Image
- `fix-qwen-workflow.py` → Peut corriger les workflows GenAI-Image
- `comfyui-client-helper.py` → Peut gérer ComfyUI pour GenAI-Image

---

## 📈 Plan de Consolidation Technique

### Phase 1 : Préparation et Analyse
1. **Création répertoire de travail** : `scripts/genai-image-consolidated/`
2. **Backup des scripts sources** : Archive dans `historical-migrations/`
3. **Analyse des dépendances** : Identifier les imports et librairies communes

### Phase 2 : Développement Scripts Consolidés
1. **`setup-docker-compose.ps1** : Fusion des 5 scripts Docker
2. **`diagnostic-genai-image.py` : Fusion des 6 scripts diagnostic
3. **`configure-qwen-setup.py` : Fusion des 3 scripts Qwen  
4. **`deploy-genai-image.py` : Fusion des 2 scripts déploiement

### Phase 3 : Validation et Documentation
1. **Tests unitaires** : Validation de chaque script consolidé
2. **Documentation** : README et aide intégrée
3. **Intégration** : Tests avec environnement existant

---

## 🎯 Résultats Attendus

**Réduction de complexité** : 16 scripts → 4 scripts (75% de réduction)  
**Amélioration maintenabilité** : Scripts unifiés avec documentation complète  
**Standardisation** : Conformité avec patterns genai-auth établis  
**Réutilisation** : Fonctionnalités modulaires et évolutives  

---

## 📝 Notes SDDD

**Grounding sémantique effectué** : ✅ Patterns de consolidation identifiés et validés  
**Documentation de référence** : `RAPPORT_FINAL_CONSOLIDATION_SCRIPTS_GENAI_AUTH_SDDD.md`  
**Prochaine étape** : Création des scripts consolidés selon matrice établie  

**Statut** : Prêt pour développement des scripts consolidés