# Plan de Consolidation Scripts Qwen - Diagnostic & Correction

## 📋 Contexte

- **Problème principal** : Échec du workflow JSON Qwen avec ImportError structurel
- **Scripts existants** : 12+ scripts dispersés dans `scripts/genai-auth/` et `MyIA.AI.Notebooks/GenAI/`
- **Objectif** : Consolider en 4 scripts essentiels avec documentation SDDD

## 🎯 Scripts Essentiels à Conserver

### 1. `diagnostic-qwen-complete.py`
**Rôle** : Diagnostic complet de l'environnement Qwen/ComfyUI
**Fonctionnalités** :
- Analyse structurelle des packages Python
- Validation des imports relatifs/absolus
- Inspection des signatures de nodes ComfyUI
- Génération de rapport détaillé

### 2. `fix-qwen-workflow.py`
**Rôle** : Application des corrections structurelles identifiées
**Fonctionnalités** :
- Création automatique des fichiers `__init__.py` manquants
- Correction des imports relatifs en imports absolus
- Restructuration du package ComfyUI-QwenImageWanBridge
- Validation post-correction

### 3. `validate-qwen-solution.py`
**Rôle** : Validation complète de la solution Qwen
**Fonctionnalités** :
- Test des workflows JSON après correction
- Validation des imports corrigés
- Vérification de l'intégration ComfyUI
- Génération de rapport de validation

### 4. `comfyui-client-helper.py`
**Rôle** : Utilitaire réutilisable pour investigations ComfyUI futures
**Fonctionnalités** :
- Client HTTP pour ComfyUI API
- Gestion des workflows JSON
- Upload de fichiers temporaires
- Monitoring des réponses serveur

## 🏗️ Structure de Documentation SDDD

```
docs/suivis/genai-image/
├── README.md                           # Vue d'ensemble et index
├── 01-diagnostic/                      # Scripts et documentation diagnostic
│   ├── diagnostic-qwen-complete.md
│   └── schema-diagnostics.json
├── 02-corrections/                      # Solutions et corrections appliquées
│   ├── fix-qwen-workflow.md
│   ├── import-error-resolution.md
│   └── package-structure-fix.json
├── 03-validation/                       # Tests et validation
│   ├── validate-qwen-solution.md
│   └── test-results-schema.json
├── 04-utils/                           # Utilitaires réutilisables
│   ├── comfyui-client-helper.md
│   └── api-patterns.json
└── 99-references/                      # Références techniques
    ├── comfyui-node-development.md
    ├── python-packaging-best-practices.md
    └── qwen-integration-guide.md
```

## 🚀 Plan d'Action en 3 Phases

### Phase 1 : Corrections Structurelles
**Objectif** : Résoudre l'ImportError racine

1. **Créer les fichiers `__init__.py` manquants** :
   ```python
   # /workspace/ComfyUI/custom_nodes/ComfyUI-QwenImageWanBridge/__init__.py
   __all__ = ['nodes']
   
   # /workspace/ComfyUI/custom_nodes/ComfyUI-QwenImageWanBridge/nodes/__init__.py
   from .qwen_wrapper_nodes import QwenImageSamplerNode
   from .qwen_wrapper_loaders import QwenVLCLIPLoader
   from .qwen_wrapper_base import QwenWrapperBase
   __all__ = ['QwenImageSamplerNode', 'QwenVLCLIPLoader', 'QwenWrapperBase']
   ```

2. **Corriger les imports relatifs** dans `qwen_wrapper_loaders.py` :
   ```python
   # Avant (problématique)
   from .qwen_wrapper_base import QwenWrapperBase, QWEN_VAE_CHANNELS
   
   # Après (corrigé)
   from ComfyUI_QwenImageWanBridge.nodes.qwen_wrapper_base import QwenWrapperBase, QWEN_VAE_CHANNELS
   ```

3. **Valider la structure du package** complet

### Phase 2 : Validation de Solution
**Objectif** : Confirmer que les corrections résolvent le problème

1. **Tester les workflows JSON** avec `validate-qwen-solution.py`
2. **Vérifier l'intégration ComfyUI** via API
3. **Générer rapport de validation** complet

### Phase 3 : Nettoyage et Documentation
**Objectif** : Finaliser la consolidation

1. **Archiver les anciens scripts** dans `scripts/genai-auth/archive/`
2. **Créer la documentation SDDD** complète
3. **Mettre à jour les scripts réutilisables** pour futures investigations

## 📊 Métriques de Succès

- **Réduction scripts** : 12+ → 4 (66% de réduction)
- **Couverture fonctionnelle** : 100% (diagnostic, correction, validation, utilitaires)
- **Réutilisabilité** : Élevée (scripts modulaires pour futures investigations ComfyUI)
- **Documentation** : Complète SDDD avec schémas JSON et guides techniques

## ⚠️ Points d'Attention

- **Backup obligatoire** : Avant toute modification structurelle
- **Test en isolement** : Valider chaque correction séparément
- **Validation ComfyUI** : Vérifier que les nodes sont bien détectés après correction
- **Documentation synchrone** : Maintenir docs à jour avec les évolutions

---
*Créé le : 2025-10-28*
*Auteur : Roo Architect*
*Version : 1.0*