# Guide Réparation MCP - Phase 17

**Date de création**: 2025-10-17  
**Version**: 1.0  
**Auteur**: SDDD Process  
**Scope**: Réparation MCPs `roo-state-manager` et `jupyter-papermill`

---

## Table des Matières

1. [Introduction](#1-introduction)
2. [Symptômes Pannes](#2-symptômes-pannes)
3. [Diagnostic](#3-diagnostic)
4. [Solutions Détaillées](#4-solutions-détaillées)
5. [Prévention Futures Pannes](#5-prévention-futures-pannes)
6. [Troubleshooting](#6-troubleshooting)
7. [Scripts Automatisés](#7-scripts-automatisés)

---

## 1. Introduction

Ce guide documente les procédures de réparation des MCPs (Model Context Protocol) utilisés dans l'environnement de développement Roo/VS Code.

### MCPs Couverts

- **roo-state-manager** (TypeScript/Node.js) : Gestion état agent
- **jupyter-papermill** (Python) : Opérations notebooks Jupyter

### Quand Utiliser Ce Guide

- ❌ MCP ne démarre pas (erreur dans logs VS Code)
- ❌ Extension Roo affiche erreur "Invalid configuration"
- ❌ Outils MCP non disponibles dans interface
- ❌ Logs montrent `ModuleNotFoundError` ou `ENOENT`

---

## 2. Symptômes Pannes

### 2.1. MCP roo-state-manager

#### Symptôme 1: MODULE_NOT_FOUND

**Logs VS Code Extension Host**:
```
Error: Cannot find module 'D:\Dev\roo-extensions\mcps\internal\servers\roo-state-manager\dist\index.js'
```

**Cause**: Path hardcodé incorrect dans `mcp_settings.json`

**Impact**: MCP ne démarre pas du tout

---

#### Symptôme 2: ENOENT .env File

**Logs VS Code Extension Host**:
```
Error: ENOENT: no such file or directory, open 'D:\Dev\roo-extensions\mcps\internal\servers\roo-state-manager\build\.env'
```

**Cause**: Bug path resolution `.env` dans code TypeScript compilé

**Impact**: MCP démarre puis crash immédiatement

---

### 2.2. MCP jupyter-papermill

#### Symptôme 1: ModuleNotFoundError

**Logs VS Code Extension Host**:
```
C:\Python313\python.exe: Error while finding module specification for 'papermill_mcp.main' (ModuleNotFoundError: No module named 'papermill_mcp')
```

**Cause**: Packages Python manquants OU `PYTHONPATH` non configuré

**Impact**: MCP ne démarre pas

---

#### Symptôme 2: Connection Closed

**Logs VS Code Extension Host**:
```
Invalid configuration for MCP server "jupyter": McpError: MCP error -32000: Connection closed
```

**Cause**: Logs envoyés sur `stdout` au lieu de `stderr` → corruption protocole MCP stdio

**Impact**: MCP démarre puis se termine immédiatement

---

## 3. Diagnostic

### 3.1. Vérification Logs VS Code

**Localisation**: VS Code → View → Output → Extension Host

**Chercher**:
- `[error]` lignes contenant nom MCP
- `ModuleNotFoundError`
- `ENOENT`
- `Connection closed`

---

### 3.2. Diagnostic MCP roo-state-manager

#### Étape 1: Vérifier Build

```powershell
Test-Path "D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager/build/index.js"
```

**Attendu**: `True`

**Si `False`**: Recompiler TypeScript (voir [Solution 2.1](#41-solution-roo-state-manager-build))

---

#### Étape 2: Vérifier Fichier .env

```powershell
Test-Path "D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager/.env"
```

**Attendu**: `True`

**Si `False`**: Créer fichier `.env` (voir [Solution 2.2](#42-solution-roo-state-manager-env))

---

#### Étape 3: Vérifier Configuration mcp_settings.json

**Fichier**: `C:/Users/[USERNAME]/AppData/Roaming/Code/User/globalStorage/rooveterinaryinc.roo-cline/settings/mcp_settings.json`

**Chercher section**:
```json
"roo-state-manager": {
  "args": ["/c", "node", "D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager/build/index.js"]
}
```

**Vérifier**:
- Path doit pointer vers `build/index.js` (PAS `dist/index.js`)
- Path doit être absolu et correct

---

### 3.3. Diagnostic MCP jupyter-papermill

#### Étape 1: Vérifier Packages Python

```powershell
C:\Python313\python.exe -m pip list | Select-String -Pattern "papermill|jupyter|mcp|fastmcp"
```

**Attendu**: 4 packages listés (papermill, jupyter, mcp, fastmcp)

**Si manquants**: Installer packages (voir [Solution 3.1](#43-solution-jupyter-papermill-packages))

---

#### Étape 2: Test Import Module

```powershell
pwsh -c "cd 'D:/Dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server'; C:\Python313\python.exe -c 'import papermill_mcp; print(\"OK\")'"
```

**Attendu**: `OK`

**Si erreur**: Vérifier `PYTHONPATH` (voir [Solution 3.3](#45-solution-jupyter-papermill-pythonpath))

---

#### Étape 3: Test Démarrage Manuel

```powershell
pwsh -c "cd 'D:/Dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server'; C:\Python313\python.exe -m papermill_mcp.main --help"
```

**Attendu**: Logs montrant "36 CONSOLIDATED TOOLS"

**Si erreur**: Vérifier logs stderr (voir [Solution 3.2](#44-solution-jupyter-papermill-logs))

---

## 4. Solutions Détaillées

### 4.1. Solution roo-state-manager: Build

**Problème**: Build TypeScript manquant ou obsolète

**Commandes**:
```powershell
cd D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager
npm install
npm run build
```

**Validation**:
```powershell
Test-Path "build/index.js"  # Doit retourner True
```

---

### 4.2. Solution roo-state-manager: .env

**Problème**: Fichier `.env` manquant

**Commande**:
```powershell
cd D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager

@"
# Configuration MCP roo-state-manager
# [Ajouter variables nécessaires ici]
"@ | Out-File -FilePath ".env" -Encoding UTF8
```

**Validation**:
```powershell
Test-Path ".env"  # Doit retourner True
```

---

### 4.3. Solution roo-state-manager: Bug Path .env

**Problème**: Code cherche `.env` dans `build/` au lieu de racine projet

**Fichier à modifier**: `src/index.ts`

**Ligne ~34** - Avant:
```typescript
dotenv.config({ path: path.join(__dirname, '.env') });
```

**Ligne ~34** - Après:
```typescript
// CRITICAL FIX: Go up one level from build/ to project root
dotenv.config({ path: path.join(__dirname, '..', '.env') });
```

**Après modification**:
```powershell
cd D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager
npm run build  # Recompiler pour appliquer fix
```

**Validation**:
```powershell
# Redémarrer VS Code et vérifier logs Extension Host
# Attendu: Pas d'erreur ENOENT .env
```

---

### 4.4. Solution roo-state-manager: mcp_settings.json

**Problème**: Path incorrect dans configuration VS Code

**Fichier**: `C:/Users/[USERNAME]/AppData/Roaming/Code/User/globalStorage/rooveterinaryinc.roo-cline/settings/mcp_settings.json`

**Section à corriger**:
```json
"roo-state-manager": {
  "disabled": false,
  "args": [
    "/c",
    "node",
    "D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager/build/index.js"
  ],
  "command": "cmd",
  "transportType": "stdio"
}
```

**Points clés**:
- Path doit pointer vers `build/index.js` (PAS `dist/`)
- Utiliser slashes `/` (même sur Windows)
- Path doit être absolu

**Validation**:
```powershell
# Redémarrer VS Code
# Vérifier logs Extension Host → Pas d'erreur MODULE_NOT_FOUND
```

---

### 4.5. Solution jupyter-papermill: Packages

**Problème**: Packages Python manquants

**Commande**:
```powershell
C:\Python313\python.exe -m pip install papermill jupyter mcp fastmcp
```

**Validation**:
```powershell
C:\Python313\python.exe -m pip list | Select-String -Pattern "papermill|jupyter|mcp|fastmcp"

# Attendu:
# fastmcp         X.X.X
# jupyter         X.X.X
# mcp             X.X.X
# papermill       X.X.X
```

---

### 4.6. Solution jupyter-papermill: Logs stderr

**Problème**: Logs envoyés sur `stdout` → corruption MCP stdio

**Fichier à modifier**: `papermill_mcp/main.py`

**Ligne ~40** - Avant:
```python
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout)  # ❌ ERREUR
    ]
)
```

**Ligne ~40** - Après:
```python
# Configure logging with enhanced format
# CRITICAL FIX: Use stderr for logs to avoid corrupting MCP stdio protocol
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stderr)  # ✅ CORRECT
    ]
)
```

**Validation**:
```powershell
# Redémarrer VS Code
# Vérifier logs Extension Host → Pas d'erreur "Connection closed"
```

---

### 4.7. Solution jupyter-papermill: PYTHONPATH

**Problème**: Extension VS Code ne trouve pas module `papermill_mcp`

**Fichier**: `C:/Users/[USERNAME]/AppData/Roaming/Code/User/globalStorage/rooveterinaryinc.roo-cline/settings/mcp_settings.json`

**Section à corriger**:
```json
"jupyter": {
  "disabled": false,
  "args": [
    "/c",
    "set",
    "PYTHONPATH=D:/Dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server",
    "&&",
    "C:\\Python313\\python.exe",
    "-m",
    "papermill_mcp.main"
  ],
  "options": {
    "cwd": "D:/Dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server"
  },
  "command": "cmd",
  "transportType": "stdio"
}
```

**Points clés**:
- Commande `set PYTHONPATH=...` avant `python.exe`
- Chaînage avec `&&`
- `cwd` doit pointer vers répertoire serveur
- Path Python avec double backslashes `\\`

**Validation**:
```powershell
# Redémarrer VS Code
# Vérifier logs Extension Host → Pas d'erreur ModuleNotFoundError
```

---

## 5. Prévention Futures Pannes

### 5.1. Règles Générales MCPs

#### Règle 1: Logs TOUJOURS sur stderr

**Pour tous les MCPs Python**:
```python
logging.basicConfig(
    handlers=[logging.StreamHandler(sys.stderr)]  # ✅ TOUJOURS stderr
)
```

**Raison**: Protocole MCP stdio nécessite `stdout` propre pour communication binaire

---

#### Règle 2: Paths Absolus dans Configuration

**Dans `mcp_settings.json`**:
```json
{
  "args": ["...", "D:/Dev/absolute/path/to/server"]  // ✅ Absolu
}
```

**Éviter**:
```json
{
  "args": ["...", "./relative/path"]  // ❌ Relatif
}
```

---

#### Règle 3: PYTHONPATH Explicite pour MCPs Python

**Pattern recommandé**:
```json
"args": [
  "/c",
  "set",
  "PYTHONPATH=D:/path/to/mcp/server",
  "&&",
  "python.exe",
  "-m",
  "module.main"
]
```

---

#### Règle 4: Build TypeScript Avant Commit

**Workflow recommandé**:
```powershell
# Avant commit code TypeScript
cd path/to/mcp/typescript
npm run build
git add build/
git commit -m "..."
```

---

### 5.2. Checklist Avant Modification MCP

- [ ] Backup `mcp_settings.json`
- [ ] Si TypeScript: Vérifier `build/` à jour
- [ ] Si Python: Vérifier packages installés
- [ ] Tester en ligne de commande AVANT VS Code
- [ ] Vérifier logs sur `stderr` (pas `stdout`)
- [ ] Documenter changements

---

### 5.3. Tests Réguliers

**Fréquence**: Après chaque mise à jour MCP ou dépendances

**Script automatisé**: [`2025-10-17_03_test-validation-mcps.ps1`](scripts/2025-10-17_03_test-validation-mcps.ps1)

**Commande**:
```powershell
pwsh -c "& 'docs/suivis/genai-image/phase-17-reparation-mcp/scripts/2025-10-17_03_test-validation-mcps.ps1'"
```

**Attendu**: 10/10 tests réussis

---

## 6. Troubleshooting

### 6.1. MCP Démarre Puis Crash Immédiat

**Symptôme**: Logs montrent démarrage puis "Connection closed"

**Causes possibles**:
1. Logs sur `stdout` au lieu de `stderr`
2. Exception non catchée dans code serveur
3. Dépendance manquante

**Diagnostic**:
```powershell
# Test manuel en ligne de commande
cd path/to/mcp/server
python -m module.main --help  # Voir erreur complète
```

---

### 6.2. ModuleNotFoundError Persistant

**Symptôme**: Erreur même après installation packages

**Solutions à essayer**:
1. Vérifier version Python correcte utilisée
2. Ajouter `PYTHONPATH` dans `mcp_settings.json`
3. Vérifier `sys.path` en runtime:
   ```python
   import sys; print(sys.path)
   ```

---

### 6.3. Path Resolution Bugs

**Symptôme**: `ENOENT: no such file or directory`

**Solutions**:
1. Utiliser paths absolus
2. Pour fichiers relatifs au code:
   - Python: `os.path.join(os.path.dirname(__file__), 'relative/path')`
   - TypeScript: `path.join(__dirname, 'relative/path')`
3. Vérifier différence source vs build (TypeScript)

---

### 6.4. VS Code Ne Recharge Pas MCP

**Symptôme**: Modifications non prises en compte

**Solution**:
```powershell
# 1. Fermer tous fichiers/onglets du projet
# 2. Redémarrer VS Code (pas juste window)
# 3. Vérifier timestamp modification mcp_settings.json
```

---

## 7. Scripts Automatisés

### 7.1. Script Validation MCPs

**Fichier**: [`2025-10-17_03_test-validation-mcps.ps1`](scripts/2025-10-17_03_test-validation-mcps.ps1)

**Usage**:
```powershell
pwsh -c "& 'docs/suivis/genai-image/phase-17-reparation-mcp/scripts/2025-10-17_03_test-validation-mcps.ps1'"
```

**Tests effectués** (10 total):
- ✅ Build `roo-state-manager` existe
- ✅ Fichier `.env` présent
- ✅ 4 packages Python installés
- ✅ Module `papermill_mcp` importable
- ✅ Configuration `mcp_settings.json` valide
- ✅ Fix `PYTHONPATH` présent

**Sortie**: Rapport détaillé dans `rapports/2025-10-17_17_validation-mcps.md`

---

### 7.2. Script Diagnostic (À Créer)

**Template**:
```powershell
# TODO: Créer script diagnostic automatique
# - Vérifier tous MCPs configurés
# - Tester démarrage manuel
# - Analyser logs VS Code
# - Générer rapport problèmes
```

---

## Annexes

### A. Chemins Importants

**Configuration VS Code**:
```
C:/Users/[USERNAME]/AppData/Roaming/Code/User/globalStorage/rooveterinaryinc.roo-cline/settings/mcp_settings.json
```

**MCP roo-state-manager**:
```
D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager/
├── src/index.ts (source TypeScript)
├── build/index.js (code compilé)
└── .env (variables d'environnement)
```

**MCP jupyter-papermill**:
```
D:/Dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server/
└── papermill_mcp/main.py (point d'entrée)
```

---

### B. Commandes Utiles

**Lister MCPs configurés**:
```powershell
Get-Content "C:/Users/$env:USERNAME/AppData/Roaming/Code/User/globalStorage/rooveterinaryinc.roo-cline/settings/mcp_settings.json" | ConvertFrom-Json | Select-Object -ExpandProperty mcpServers | Get-Member -MemberType NoteProperty | Select-Object -ExpandProperty Name
```

**Tester package Python installé**:
```powershell
C:\Python313\python.exe -c "import [PACKAGE]; print([PACKAGE].__version__)"
```

**Recompiler MCP TypeScript**:
```powershell
cd D:/Dev/roo-extensions/mcps/internal/servers/[MCP_NAME]
npm run build
```

---

### C. Ressources Externes

- **Documentation MCP**: [ModelContextProtocol.io](https://modelcontextprotocol.io)
- **VS Code Extension API**: [code.visualstudio.com/api](https://code.visualstudio.com/api)
- **FastMCP Python**: [pypi.org/project/fastmcp](https://pypi.org/project/fastmcp)

---

**Version**: 1.0  
**Dernière mise à jour**: 2025-10-17  
**Maintenu par**: SDDD Process - Phase 17

*Ce guide est généré automatiquement et mis à jour après chaque réparation MCP documentée.*