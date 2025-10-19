# Grounding Sémantique Initial - Phase 17 Réparation MCP

**Date**: 2025-10-16  
**Phase**: 17 - Diagnostic + Réparation MCP jupyter-papermill  
**Objectif**: Comprendre historique problèmes MCP et solutions appliquées

---

## Recherches Effectuées

### 1. Historique MCP Jupyter-Papermill

**Requête**: `MCP jupyter-papermill diagnostic erreur NuGet dotnet-interactive papermill-coursia`

**Découvertes Clés**:

#### A. Problème Central Récurrent
- **Root cause**: Incompatibilité fondamentale entre contexte d'exécution `papermill` via MCP et processus de build .NET Interactive pour restauration NuGet
- **Pattern**: Le MCP fonctionne parfaitement pour Python, mais échoue systématiquement avec notebooks .NET nécessitant NuGet
- **Différence critique**: 
  - `papermill` via MCP = processus Python isolé, environnement minimaliste
  - `jupyter nbconvert` direct = terminal utilisateur, environnement complet

#### B. Évolution Architecture MCP

**Serveur Node.js (Abandonné)** - Phases 06-13:
- Architecture: Client API, connexion serveur Jupyter externe
- Bibliothèque: `@jupyterlab/services`
- Problèmes:
  - Instabilité SDK `@modelcontextprotocol/sdk`
  - Plantages silencieux
  - Échecs PATH pour commande `jupyter`
- Statut: Non fonctionnel, abandonné

**Serveur Python/Papermill (Actif)** - Phases 14+:
- Architecture: Hôte d'exécution, lance `papermill` comme processus enfant direct
- Framework: FastMCP + Python 3.10+
- Environnement: `mcp-jupyter-py310` (conda)
- Problème initial: Conflit `asyncio` avec VS Code → **RÉSOLU** par API directe non-async
- **Problème fondamental actuel**: Kernel .NET = sous-processus MCP, hérite environnement isolé → casse MSBuild NuGet

#### C. Solutions Tentées (Phases 15-26)

**Solution A - Variables Environnement Exhaustives** (Phase 15, 19, 24, 26):
```json
{
  "env": {
    "DOTNET_ROOT": "C:\\Program Files\\dotnet",
    "NUGET_PACKAGES": "C:\\Users\\jsboi\\.nuget\\packages",
    "MSBuildExtensionsPath": "C:\\Program Files\\dotnet\\sdk\\9.0.305",
    "MSBuildSDKsPath": "C:\\Program Files\\dotnet\\sdk\\9.0.305\\Sdks",
    "MSBuildToolsPath": "C:\\Program Files\\dotnet\\sdk\\9.0.305",
    "CONDA_EXE": "C:\\ProgramData\\miniconda3\\Scripts\\conda.exe",
    // + 17 variables CONDA critiques
  }
}
```
- **Résultat**: Amélioration partielle, mais problème persiste pour NuGet complexe

**Solution B - Architecture subprocess** (Phase 26):
- Utilisation `subprocess.run()` au lieu de API papermill directe
- Objectif: Héritage complet environnement système
- **Statut documentation**: Solution "définitive retrouvée" mais validation à confirmer

**Solution C - Approche Hybride** (Phase 20, 25):
- Python → MCP Papermill (fonctionne parfaitement)
- .NET avec NuGet → `jupyter nbconvert` direct ou `execute_command`
- **Statut**: Recommandation architecturale officielle

#### D. État Actuel Infrastructure

**MCP jupyter-papermill-mcp-server**:
- **Localisation**: `D:/dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server`
- **Module principal**: `papermill_mcp.main`
- **Configuration**: `C:/Users/jsboi/AppData/Roaming/Code/User/globalStorage/rooveterinaryinc.roo-cline/settings/mcp_settings.json`
- **Outils exposés**: 22+ outils (notebooks, kernels, execution)
- **Architecture actuelle**: subprocess_isolation
- **Environnement**: mcp-jupyter-py310

**papermill-coursia** (Custom wrapper):
- **Localisation**: `notebook-infrastructure/papermill-coursia`
- **Composants**:
  - `core/executor.py` - Moteur d'exécution robuste
  - `cli/papermill_coursia.py` - Interface CLI complète
  - `requirements.txt` - Dépendances optimisées
- **Statut**: Infrastructure personnalisée pour exécution notebooks

---

### 2. Architecture MCP Actuelle

**Requête**: `MCP papermill-coursia architecture installation configuration requirements`

**Découvertes Clés**:

#### A. Configuration MCP Production

**Fichier**: `mcp_settings.json`

**Paramètres Critiques**:
- `enabled`: true
- `architecture`: subprocess_isolation (CRITIQUE)
- `environment`: mcp-jupyter-py310 (CRITIQUE)
- `tools`: 22+ (TOUS PRÉSERVÉS)
- `timeout`: unlimited (ExecutionManager async)
- `transportType`: stdio
- `autoStart`: true
- `command`: conda
- `args`: ["run", "-n", "mcp-jupyter-py310", "python", "-m", "papermill_mcp.main"]

#### B. Chaîne Dépendances Critique

```
VS Code Extension Roo
  ↓
McpHub.ts (singleton orchestrateur)
  ↓
jupyter-papermill-mcp-server (processus Python isolé)
  ↓
papermill.execute_notebook() ou subprocess.run()
  ↓
Kernel Jupyter (.NET Interactive ou Python)
  ↓
MSBuild + NuGet (pour .NET) ← POINT DE DÉFAILLANCE
```

**Points de Défaillance Identifiés**:
1. **Isolation environnement**: Processus MCP n'hérite pas variables système Windows
2. **Création projet temporaire**: Échoue silencieusement dans environnement MCP isolé
3. **GetRestoreSettingsTask**: Reçoit `path1=null` car projet inexistant
4. **Erreur finale**: `Value cannot be null. (Parameter 'path1')`

#### C. Principe ZÉRO RÉGRESSION

**Contraintes Absolues** (integration-roadmap.md):
- ✅ Préserver les 22+ outils MCP existants
- ✅ Maintenir ExecutionManager async (timeouts illimités)
- ✅ Conserver architecture subprocess isolation
- ✅ Garder compatibilité Papermill-CoursIA
- ✅ Protéger notebooks existants

**Implication**: Toute réparation doit être **non-intrusive** et **rétrocompatible**

---

### 3. Outils Diagnostic Disponibles

**Requête**: `roo-state-manager logs diagnostic MCP troubleshooting`

**Découvertes Clés**:

#### A. Capacités roo-state-manager

**Outils MCP Disponibles**:
- `manage_mcp_settings`: Gestion configuration MCP
  - Actions: update_server, get_server, list_servers
  - Modification directe `mcp_settings.json`
  
- `touch_mcp_settings`: Redémarrage MCPs après modification config

- `rebuild_and_restart_mcp`: Build + redémarrage serveur MCP
  - Limitation: Détection automatique type projet à améliorer
  - Limitation: `project_path` non paramétrable

**Outils Recommandés NON IMPLÉMENTÉS** (architecture_mcp_roo.md):
- `get_mcp_server_state`: Inspection état interne serveurs MCP
  - Retournerait: status, config, tools, errorHistory
  - **CRITIQUE**: Aurait rendu diagnostic beaucoup plus direct
  
#### B. Logs MCP Actuels

**Mécanisme**:
- Logs capturés exclusivement depuis flux `stderr` processus MCP
- Stockés dans `errorHistory` objet serveur avec timestamps
- **Limitation**: Pas de visualisation simple depuis interface
- **Limitation**: Pas de fichier log centralisé dédié MCPs

**Accès Logs**:
- VS Code Output Channel
- Console extension VS Code (`console.error`)
- Fichiers logs temporaires notebooks: `github-projects-mcp-combined.log`

#### C. Configuration Hiérarchique

**Ordre Priorité**:
1. `.roo/mcp.json` (projet) - surcharge globale
2. `mcp_settings.json` (global) - configuration de base

**Variables d'environnement**:
- `PYTHONPATH`: Influence imports Python serveur MCP
- Variables MSBuild: Nécessaires pour .NET Interactive
- Variables CONDA: Essentielles pour environnement isolé

---

## État Attendu vs Réel

### État Attendu (Documentation Phase 26)

**MCP jupyter-papermill devrait**:
- ✅ Exécuter notebooks Python sans problème
- ✅ Exécuter notebooks .NET simples (sans NuGet)
- ✅ Exécuter notebooks .NET complexes avec NuGet (via subprocess + variables complètes)
- ✅ Fonctionner avec configuration "définitive" appliquée

### État Réel (À Confirmer par Diagnostic)

**Symptômes possibles**:
- MCP ne démarre pas du tout
- MCP démarre mais outils inaccessibles
- Notebooks Python fonctionnent, .NET échouent
- Configuration mcp_settings.json corrompue ou incomplète
- Variables environnement critiques manquantes
- Architecture subprocess non implémentée dans code Python

**Gap Potentiels**:
1. Configuration `mcp_settings.json` non à jour avec Solution B (subprocess)
2. Code Python `papermill_mcp.main` utilise toujours API directe au lieu de subprocess
3. Variables environnement manquantes ou chemins incorrects
4. Environnement conda `mcp-jupyter-py310` corrompu ou incomplet
5. Fichier `papermill-coursia` manquant ou non configuré

---

## Mise à Jour TODO

**Ajustements Suite Découvertes**:

✅ **Confirmation Pattern Historique**: Problème NuGet .NET via MCP est **récurrent et documenté** (Phases 06-26)

🔍 **Actions Prioritaires Identifiées**:
1. Vérifier si configuration Phase 26 (subprocess + variables) réellement appliquée
2. Inspecter code Python `main_fastmcp.py` ou `main.py` pour architecture subprocess
3. Valider environnement conda `mcp-jupyter-py310` complet
4. Tester MCP avec notebook Python simple (baseline fonctionnel)
5. Tester MCP avec notebook .NET sans NuGet (regression test)
6. Tester MCP avec notebook .NET + NuGet (test critique)

⚠️ **Risques Identifiés**:
- Documentation Phase 26 décrit solution "retrouvée" mais peut ne pas être implémentée
- Modifications configuration peuvent avoir été perdues lors migrations
- Multiples fichiers `main.py` / `main_fastmcp.py` / `main_simple.py` créent confusion
- Variables environnement Windows peuvent avoir changé (SDK .NET mis à jour)

---

## Prochaines Étapes

**Partie 2**: Grounding Conversationnel via roo-state-manager
- Récupérer historique complet tâches MCP
- Examiner détails techniques réparations passées
- Synthétiser patterns pannes récurrentes

**Partie 3**: Diagnostic Technique via Script PowerShell
- Exécuter script diagnostic complet système
- Valider environnement Python/Conda
- Tester import papermill
- Vérifier dotnet-interactive
- Tester exécution notebook minimal

**Objectif Phase 17**: Rétablir MCP jupyter-papermill **opérationnel pour notebooks Python ET .NET** en appliquant solution définitive validée.

---

**Document**: [`2025-10-16_17_01_grounding-semantique-initial.md`](docs/suivis/genai-image/phase-17-reparation-mcp/2025-10-16_17_01_grounding-semantique-initial.md)  
**Auteur**: SDDD Process - Phase 17  
**Statut**: ✅ Grounding sémantique initial complété