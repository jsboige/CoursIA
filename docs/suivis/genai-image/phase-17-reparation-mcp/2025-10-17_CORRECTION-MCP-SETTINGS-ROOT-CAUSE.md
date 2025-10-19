# Correction MCP Settings - Root Cause Identifiée

**Date**: 2025-10-17 16:35
**Phase**: 17 - Réparation MCP
**Status**: ✅ CORRECTION APPLIQUÉE

---

## ROOT CAUSE IDENTIFIÉE

### Problème Initial
Le MCP `roo-state-manager` échouait systématiquement avec l'erreur :
```
Error: Cannot find module 'D:\Dev\roo-extensions\mcps\internal\servers\roo-state-manager\build\src\index.js'
```

### Diagnostic Incorrect Initial
J'avais initialement diagnostiqué que le problème venait du `package.json` du serveur MCP, où la propriété `"main"` pointait vers `"build/src/index.js"` au lieu de `"build/index.js"`.

**❌ Ce diagnostic était PARTIELLEMENT INCORRECT.**

### Root Cause Réelle
Le vrai problème était dans **le fichier de configuration VS Code des MCPs** :
```
C:/Users/jsboi/AppData/Roaming/Code/User/globalStorage/rooveterinaryinc.roo-cline/settings/mcp_settings.json
```

Ce fichier contenait un chemin **hardcodé incorrect** (ligne 251) :
```json
"roo-state-manager": {
  "command": "node",
  "args": [
    "D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager/build/src/index.js"
  ],
  ...
}
```

**VS Code n'utilise PAS le `package.json` du serveur MCP**, il utilise directement ce chemin hardcodé dans `mcp_settings.json`.

---

## CORRECTION APPLIQUÉE

### Fichier Modifié
`C:/Users/jsboi/AppData/Roaming/Code/User/globalStorage/rooveterinaryinc.roo-cline/settings/mcp_settings.json`

### Changement (ligne 250-252)
**AVANT** :
```json
"args": [
  "D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager/build/src/index.js"
]
```

**APRÈS** :
```json
"args": [
  "D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager/build/index.js"
]
```

### Explication Technique
- Le build TypeScript produit : `build/index.js` (structure plate)
- L'ancien chemin cherchait : `build/src/index.js` (structure imbriquée inexistante)
- La correction aligne le chemin avec la structure réelle du build

---

## PROCHAINES ÉTAPES

1. **Redémarrer VS Code** pour recharger `mcp_settings.json`
2. **Valider** que `roo-state-manager` démarre sans erreur
3. **Passer** à la réparation du MCP `jupyter-papermill` (erreur `papermill_mcp`)

---

## LEÇONS APPRISES

### Pour Diagnostic Futur
1. ✅ **Toujours vérifier `mcp_settings.json` en priorité** lors d'erreurs MCP
2. ✅ Les chemins hardcodés dans `mcp_settings.json` **remplacent** les configurations `package.json`
3. ✅ Un redémarrage VS Code est **impératif** après modification de `mcp_settings.json`

### Architecture MCP Extension
- L'extension Roo-Cline stocke sa configuration dans `globalStorage`
- Le fichier `mcp_settings.json` est la **source de vérité** pour les chemins MCP
- Les serveurs MCP individuels n'ont **pas besoin** de `package.json` correctement configuré pour les chemins

---

## DOCUMENTATION ASSOCIÉE

- [`2025-10-17_RAPPORT-ETAT-ACTUEL-PHASE17.md`](2025-10-17_RAPPORT-ETAT-ACTUEL-PHASE17.md) : Contexte complet investigation
- [`2025-10-16_17_02_diagnostic-erreurs-mcps.md`](2025-10-16_17_02_diagnostic-erreurs-mcps.md) : Diagnostic initial 2 MCPs cassés
- [`2025-10-17_08_10_succes-correction-package-json.md`](2025-10-17_08_10_succes-correction-package-json.md) : Tentative correction package.json (inefficace)

---

**Validation**: Attente redémarrage VS Code + confirmation démarrage MCP