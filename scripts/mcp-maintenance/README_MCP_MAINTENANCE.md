# 🔧 Infrastructure de Maintenance MCP - Projet CoursIA

**Date de création :** 18 septembre 2025  
**Méthode :** SDDD (Semantic-Documentation-Driven-Design) avec Triple Grounding  
**Mission :** Centralisation et organisation des artefacts de l'investigation MCP-NuGet

---

## 🎯 Vue d'Ensemble

Cette infrastructure centralise tous les fichiers, configurations et documentation relatifs à la résolution des problèmes d'incompatibilité entre l'environnement MCP (Model Context Protocol) et la restauration de packages NuGet par .NET Interactive lors de l'exécution de notebooks.

### Architecture SDDD

```
notebook-infrastructure/mcp-maintenance/
├── debug-notebooks/        # Notebooks de diagnostic et de test MCP
├── config/                 # Configurations critiques et analyses d'environnement  
├── scripts/               # Scripts de validation et d'environnement
└── docs/                  # Documentation technique spécialisée
```

---

## 📂 Répertoire `debug-notebooks/`

### Notebooks de Diagnostic MCP
- **`debug-microsoft-ml-minimal.ipynb`** : Test minimal avec Microsoft.ML
- **`debug-nuget-path1-minimal.ipynb`** : Investigation de l'erreur "path1 null"
- **`debug-simple-package.ipynb`** : Test de base pour packages NuGet
- **`debug-gradebook-packages.ipynb`** : Validation avec packages complexes
- **`debug-preinstalled-packages.ipynb`** : Test avec cache NuGet pré-rempli
- **`diagnostic-environnement-mcp.ipynb`** : Audit complet de l'environnement MCP

### Objectif
Ces notebooks servent de **suite de tests de régression** pour valider le bon fonctionnement de l'environnement MCP avec .NET Interactive et NuGet.

---

## ⚙️ Répertoire `config/`

### Fichiers de Configuration Critiques
- **`ETAPE-2-VARIABLES-CRITIQUES-INJECTION.md`** : Liste exhaustive des variables d'environnement requises
- **`ETAPE-3-CHANGEMENTS-APPLIQUES-RESOLUTION-MCP-NUGET.md`** : Documentation des modifications appliquées
- **`analyse-comparaison-environnements.md`** : Analyse comparative des environnements fonctionnels vs défaillants

### Utilisation
Ces configurations documentent la **solution définitive** pour l'intégration MCP-NuGet, incluant :
- Variables d'environnement CONDA critiques (17+ variables)
- Configuration `mcp_settings.json` complète
- Architecture subprocess isolation requise

---

## 🛠️ Répertoire `scripts/`

### Scripts de Validation
- **`validate_environment.py`** : Script de validation automatique de l'environnement MCP

### Extension Future
Emplacement pour développer des outils de :
- Diagnostic automatique des problèmes MCP
- Validation de configuration
- Tests d'intégration continue

---

## 📋 Répertoire `docs/`

### Documentation Technique Spécialisée
- **`24-RESOLUTION-TECHNIQUE-NUGET-TARGETS-PATH1-NULL.md`** : Analyse technique de l'erreur "path1 null"
- **`26-RESOLUTION-DEFINITIVE-MCP-NUGET-SOLUTION-RETROUVEE.md`** : Solution complète retrouvée par analyse archéologique

### Complémentarité
Cette documentation technique complète celle disponible dans `docs/_archives/investigation-mcp-nuget/` (21 documents séquentiels, archives).

---

## 🔍 Contexte Historique de l'Investigation

### Problème Identifié
**Incompatibilité architecturale** entre l'environnement isolé du MCP et le mécanisme de build externe de .NET Interactive pour la restauration NuGet.

### Symptômes
- ✅ **Notebooks Python** : Fonctionnement parfait via MCP
- ✅ **Notebooks .NET sans NuGet** : Fonctionnement parfait via MCP  
- ❌ **Notebooks .NET avec NuGet** : Échecs systématiques via MCP
- ✅ **Tous types de notebooks** : Fonctionnement parfait en exécution directe (non-MCP)

### Solution Technique
**Architecture subprocess isolation** avec environnement conda `mcp-jupyter-py310` enrichi de toutes les variables système requises.

---

## 🚀 Utilisation pour Maintenance Future

### 1. Diagnostic de Problème MCP-NuGet
```bash
# Exécuter la suite de tests de régression
jupyter nbconvert --execute debug-notebooks/debug-simple-package.ipynb
jupyter nbconvert --execute debug-notebooks/debug-microsoft-ml-minimal.ipynb
```

### 2. Validation de Configuration
```bash
# Utiliser le script de validation d'environnement
python scripts/validate_environment.py
```

### 3. Référence pour Nouvelle Installation
Utiliser les fichiers `config/` comme référence pour reproduire la configuration fonctionnelle sur un nouvel environnement.

---

## 📚 Documentation Complémentaire

### Investigation Complète
Voir `docs/_archives/investigation-mcp-nuget/` pour la séquence complète de 21 documents d'investigation (docs 06-26, archives).

### Architecture Générale
Voir `architecture_mcp_roo.md` à la racine pour l'architecture globale des serveurs MCP.

### Rapports de Synthèse
- `docs/SDDD-JUPYTER-MCP-FINAL-REPORT.md` : Rapport final SDDD
- `docs/RAPPORT-NETTOYAGE-GIT-CoursIA-2025-09-14.md` : Rapport de nettoyage précédent

---

## ⚠️ Notes Importantes

### Principe de Conservation
Tous les fichiers de cette infrastructure ont été **conservés intentionnellement** car ils constituent la **mémoire technique** de la résolution du problème MCP-NuGet.

### Non-Suppression
❌ **Ne pas supprimer** ces fichiers même s'ils semblent "temporaires"  
✅ **Ils servent de référence** pour diagnostiquer de futurs problèmes similaires

### Mise à Jour
Cette infrastructure doit être **mise à jour** lors de :
- Modifications de la configuration MCP
- Évolution des serveurs MCP
- Nouveaux problèmes d'incompatibilité identifiés

---

**Maintenu selon les principes SDDD avec grounding sémantique et conversationnel**  
*Infrastructure technique critique pour la maintenance MCP du projet CoursIA*