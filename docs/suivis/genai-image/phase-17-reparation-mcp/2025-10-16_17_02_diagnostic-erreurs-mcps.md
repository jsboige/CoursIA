# Diagnostic Erreurs MCPs - Phase 17

**Date**: 2025-10-17 00:44  
**Phase**: 17 - Diagnostic + Réparation MCP  
**Status**: 🚨 2 MCPs cassés identifiés

---

## Erreurs Identifiées

### 1. MCP roo-state-manager - MODULE_NOT_FOUND

**Erreur**:
```
Error: Cannot find module 'D:\Dev\roo-extensions\mcps\internal\servers\roo-state-manager\build\src\index.js'
    at Function._resolveFilename (node:internal/modules/cjs/loader:1405:15)
```

**Root Cause**:
- Fichier `build/src/index.js` manquant
- Build TypeScript non exécuté ou corrompu
- Serveur MCP TypeScript/Node.js

**Impact**:
- Outil roo-state-manager indisponible
- Impossible de gérer configurations MCP via outil
- Impossible d'accéder logs conversationnels

---

### 2. MCP jupyter (jupyter-papermill) - MODULE_NOT_FOUND

**Erreur**:
```
C:\Python313\python.exe: Error while finding module specification for 'papermill_mcp.main' 
(ModuleNotFoundError: No module named 'papermill_mcp')
```

**Root Cause**:
- Module `papermill_mcp` non trouvé par Python
- `PYTHONPATH` incorrect ou manquant
- Python 3.13 utilisé au lieu de conda `mcp-jupyter-py310`
- Serveur MCP situé dans `D:\Dev\roo-extensions\mcps\internal\servers\jupyter-papermill-mcp-server`

**Impact**:
- MCP jupyter-papermill totalement non fonctionnel
- Impossibilité exécuter notebooks via MCP
- Fonctionnalités Papermill inaccessibles

---

## Analyse Configuration MCP

### Configuration roo-state-manager (À Vérifier)

**Fichier attendu**: `mcp_settings.json`

**Configuration probable**:
```json
{
  "roo-state-manager": {
    "command": "node",
    "args": ["D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager/build/src/index.js"],
    "transportType": "stdio"
  }
}
```

**Problème**: Fichier `build/src/index.js` inexistant

---

### Configuration jupyter-papermill (À Vérifier)

**Fichier attendu**: `mcp_settings.json`

**Configuration probable actuelle**:
```json
{
  "jupyter": {
    "command": "C:\\Python313\\python.exe",
    "args": ["-m", "papermill_mcp.main"],
    "transportType": "stdio"
  }
}
```

**Problèmes identifiés**:
1. **Python 3.13 utilisé** au lieu de conda `mcp-jupyter-py310`
2. **PYTHONPATH manquant** pour module `papermill_mcp`
3. **Configuration incorrecte** vs documentation Phase 06-26

**Configuration attendue** (selon doc Phase 12-26):
```json
{
  "jupyter-papermill-mcp-server": {
    "transportType": "stdio",
    "autoStart": true,
    "disabled": false,
    "command": "conda",
    "args": ["run", "-n", "mcp-jupyter-py310", "python", "-m", "papermill_mcp.main"],
    "env": {
      "PYTHONPATH": "D:/dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server"
    }
  }
}
```

---

## Plan de Réparation

### Réparation 1: roo-state-manager

**Étapes**:
1. Vérifier existence répertoire `D:\Dev\roo-extensions\mcps\internal\servers\roo-state-manager`
2. Vérifier présence `package.json` et `tsconfig.json`
3. Exécuter build TypeScript:
   ```bash
   cd D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager
   npm install
   npm run build
   ```
4. Valider présence fichier `build/src/index.js` après build
5. Redémarrer MCP via Roo

**Alternative**: Si répertoire manquant, désactiver temporairement le serveur dans `mcp_settings.json`

---

### Réparation 2: jupyter-papermill

**Étapes**:
1. Vérifier configuration `mcp_settings.json` actuelle
2. Corriger configuration pour utiliser conda + PYTHONPATH:
   ```json
   {
     "jupyter": {
       "transportType": "stdio",
       "autoStart": true,
       "disabled": false,
       "command": "conda",
       "args": ["run", "-n", "mcp-jupyter-py310", "python", "-m", "papermill_mcp.main"],
       "env": {
         "PYTHONPATH": "D:/dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server"
       }
     }
   }
   ```
3. Vérifier environnement conda `mcp-jupyter-py310` existe:
   ```bash
   conda env list | grep mcp-jupyter-py310
   ```
4. Si absent, vérifier environnement alternatif `mcp-jupyter`
5. Vérifier module `papermill_mcp` dans serveur:
   ```bash
   ls D:/dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server/papermill_mcp/
   ```
6. Redémarrer MCP via Roo

---

## Prochaines Actions

**Priorité CRITIQUE**:
1. ✅ Documenter diagnostic complet
2. 🔧 Réparer MCP roo-state-manager (rebuild TypeScript)
3. 🔧 Réparer MCP jupyter-papermill (fix configuration)
4. ✅ Valider fonctionnement 2 MCPs
5. 📝 Documenter solution pour prévention futures pannes

**Contraintes**:
- Phase 17 focus jupyter-papermill, mais roo-state-manager nécessaire pour grounding conversationnel
- Réparation simultanée recommandée
- Scripts PowerShell autonomes pour réparations

---

**Document**: [`2025-10-16_17_02_diagnostic-erreurs-mcps.md`](docs/suivis/genai-image/phase-17-reparation-mcp/2025-10-16_17_02_diagnostic-erreurs-mcps.md)  
**Auteur**: SDDD Process - Phase 17  
**Statut**: ✅ Diagnostic erreurs complété