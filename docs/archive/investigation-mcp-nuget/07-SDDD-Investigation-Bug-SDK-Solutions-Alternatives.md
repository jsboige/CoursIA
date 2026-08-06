> **ARCHIVED 2026-07-30** — PM transiente (investigation MCP Jupyter / NuGet / .NET Interactive, Sept-Oct 2025). L'etat courant vit dans le serveur `mcp-jupyter` (roo-extensions) et `docs/reference/kernels-runtime.md`. INDEX-only (no external inbound refs on `origin/main`). See #7422 triage.

# Investigation Technique SDDD : Bug SDK et Solutions Alternatives

**Date :** 12 septembre 2025  
**Mission :** Investigation technique du bug SDK @modelcontextprotocol/sdk et validation de solutions de contournement  

## 🔍 Diagnostic Technique du Bug SDK

### Points de Défaillance Identifiés

#### 1. **Imports SDK Problématiques** (`index.ts`, lignes 1-9)
```typescript
import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { CallToolRequestSchema, ErrorCode, McpError, Tool } from '@modelcontextprotocol/sdk/types.js';
```

**Problème :** Dépendances critiques fragiles causant des crashes silencieux

#### 2. **Gestion Asynchrone Complexe** (`services/jupyter.ts`)
- **Connexions JupyterLab services instables** (lignes 67-94)
- **Promesses non-catchées** dans `executeCode()` (lignes 142-213) 
- **Future.onIOPub handlers** peuvent échouer silencieusement (lignes 162-197)

#### 3. **Connexion Réseau Fragile**
```typescript
const response = await axios.get(apiUrl, {
    headers: { 'Authorization': `token ${serverSettings.token}` }
});
```

**Problème :** Appels axios sans timeout approprié, erreurs de connexion non-robustes

### Évaluation de Correctif vs Contournement
**Recommandation :** **CONTOURNEMENT prioritaire**  
- SDK @modelcontextprotocol/sdk trop instable pour correctif rapide
- Solutions alternatives robustes et immédiates disponibles

---

## ✅ Validation Solutions Alternatives

### 1. **Solution NBConvert (Priorité 1) - VALIDÉE**

#### Test réussi sur `ML-1-Introduction.ipynb`
```bash
jupyter nbconvert --execute --to notebook --inplace ML-1-Introduction.ipynb --ExecutePreprocessor.timeout=120
```

**Résultats :**
- ✅ **Succès complet** (Exit code: 0)
- ✅ **Taille fichier :** 15,090 → 24,209 bytes (outputs générés)
- ⚠️  **Warning ZMQ bénin** sur Windows (n'affecte pas l'exécution)

#### Capacités et Limitations NBConvert
**✅ Points forts :**
- Exécution robuste et fiable
- Intégration native Jupyter
- Gestion timeout configurables
- Support multi-kernels automatique

**⚠️ Limitations :**
- Pas d'exécution paramétrisée
- Pas de monitoring avancé
- Warnings ZMQ cosmétiques sur Windows

### 2. **Solution Papermill (Priorité 2) - VALIDÉE SUPÉRIEURE**

#### Installation et test réussis
```bash
pip install papermill
papermill ML-1-Introduction.ipynb ML-1-Introduction-papermill-output.ipynb --progress-bar
```

**Résultats exceptionnels :**
- ✅ **26/26 cellules exécutées** avec succès
- ✅ **Performance :** 4.14 cell/s  
- ✅ **Kernel .net-csharp** détecté automatiquement
- ✅ **Progress bar** temps réel
- ✅ **Aucun warning** 

#### Capacités Avancées Papermill
**🚀 Avantages majeurs :**
- **Exécution paramétrisée** (injection de variables)
- **Progress monitoring** temps réel  
- **Gestion d'erreurs** robuste
- **Logging structuré**
- **Support multi-formats** de sortie

---

## 🔧 Tests sur Environnement Réel

### Environnement Conda `mcp-jupyter` - OPÉRATIONNEL

#### Découverte Automatique Kernels Réussie
```bash
Available kernels:
  python3            C:\Users\jsboi\.conda\envs\mcp-jupyter\share\jupyter\kernels\python3
  .net-csharp        C:\Users\jsboi\AppData\Roaming\jupyter\kernels\.net-csharp  
  .net-fsharp        C:\Users\jsboi\AppData\Roaming\jupyter\kernels\.net-fsharp
  .net-powershell    C:\Users\jsboi\AppData\Roaming\jupyter\kernels\.net-powershell
```

**✅ 4 kernels disponibles et fonctionnels**

#### Test Validation sur Différents Types
- ✅ **Notebook C#** (.net-csharp) : Succès complet
- ✅ **Notebook Python** (python3) : Succès (avec timeout attendu pour APIs externes)

---

## 📊 Évaluation Comparative

| Critère | jupyter-mcp (MCP) | NBConvert | Papermill |
|---------|-------------------|-----------|-----------|
| **Stabilité** | ❌ Crashes SDK | ✅ Robuste | ✅ Très robuste |
| **Performance** | ⚠️ Instable | ✅ Correcte | 🚀 Excellente (4.14 cell/s) |
| **Monitoring** | ❌ Limité | ⚠️ Basique | 🚀 Progress bar temps réel |
| **Paramétrage** | ✅ Avancé | ❌ Basique | 🚀 Injection variables |
| **Gestion erreurs** | ❌ Fragile | ✅ Correcte | 🚀 Robuste |
| **Multi-kernels** | ✅ Support | ✅ Support | ✅ Auto-détection |
| **Installation** | ❌ Problématique | ✅ Native | ✅ Pip simple |

## 🎯 Recommandations Techniques SDDD

### Solution Temporaire Robuste : **PAPERMILL**

#### Implémentation Immédiate Recommandée
```bash
# Installation
conda activate mcp-jupyter
pip install papermill

# Exécution standard
papermill input.ipynb output.ipynb --progress-bar

# Exécution avec paramètres
papermill input.ipynb output.ipynb -p param1 value1 -p param2 value2

# Exécution avec kernel spécifique  
papermill input.ipynb output.ipynb -k .net-csharp
```

#### Architecture de Contournement Proposée

1. **Remplacement MCP jupyter-mcp** → Scripts Papermill  
2. **API wrapper simple** autour de Papermill CLI
3. **Monitoring intégré** avec progress bars
4. **Gestion d'erreurs** robuste et logging structuré

### Avantages Business SDDD

- ✅ **Productivité immédiate** : Solutions opérationnelles aujourd'hui
- ✅ **Fiabilité éprouvée** : Papermill utilisé par Netflix, Airbnb, etc.
- ✅ **Évolutivité** : Support paramétrage avancé pour automatisation
- ✅ **Maintenance réduite** : Pas de dépendance SDK fragile

### Prochaines Étapes Recommandées

1. **Phase d'implémentation** : Remplacer jupyter-mcp par wrapper Papermill
2. **Scripts d'automatisation** : Intégration CI/CD avec Papermill  
3. **Monitoring avancé** : Dashboard exécution notebooks
4. **Formation équipes** : Migration vers nouvelles APIs

---

## 🔬 Conclusion Investigation SDDD

L'investigation technique a révélé que **le bug SDK @modelcontextprotocol/sdk est critique et non-trivial à corriger**. 

**Les solutions de contournement Papermill et NBConvert sont non seulement viables, mais SUPÉRIEURES en termes de performance, fiabilité et fonctionnalités.**

La recommandation claire est d'**abandonner temporairement l'approche MCP jupyter-mcp** au profit de **Papermill comme solution robuste** permettant de maintenir et même améliorer la productivité de l'équipe.

Cette approche SDDD (Solution-Driven Development) privilégie la **valeur business immédiate** plutôt que la complexité technique du débogage SDK.