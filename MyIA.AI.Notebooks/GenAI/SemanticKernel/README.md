# SemanticKernel - Microsoft Semantic Kernel

Serie de notebooks couvrant Microsoft Semantic Kernel, un SDK pour l'integration de LLMs dans les applications .NET et Python.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 15 |
| Kernels | .NET C#, Python |
| Duree estimee | ~4-5h |

## Notebooks

### Serie principale

| # | Notebook | Contenu | Kernel |
|---|----------|---------|--------|
| 1 | [01-SemanticKernel-Intro](01-SemanticKernel-Intro.ipynb) | Introduction, setup, premiers plugins | C# |
| 2 | [02-SemanticKernel-Advanced](02-SemanticKernel-Advanced.ipynb) | Plugins avances, chaining | C# |
| 3 | [03-SemanticKernel-Agents](03-SemanticKernel-Agents.ipynb) | Agents autonomes | C# |
| 4 | [04-SemanticKernel-Building Notebooks with clr](04-SemanticKernel-Building%20Notebooks%20with%20clr.ipynb) | Construction de notebooks via CLR | C# |
| 5 | [05-SemanticKernel-NotebookMaker](05-SemanticKernel-NotebookMaker.ipynb) | Generation automatique de notebooks | C# |

### Variantes NotebookMaker

| Notebook | Description |
|----------|-------------|
| [05-SemanticKernel-NotebookMaker-batch](05-SemanticKernel-NotebookMaker-batch.ipynb) | Version batch |
| [05-SemanticKernel-NotebookMaker-batch_parameterized](05-SemanticKernel-NotebookMaker-batch_parameterized.ipynb) | Version parametree |

### Templates

| Notebook | Description | Kernel |
|----------|-------------|--------|
| [Notebook-Template](Notebook-Template.ipynb) | Template de base | C# |
| [Workbook-Template](Workbook-Template.ipynb) | Template workbook | C# |
| [Workbook-Template-Python](Workbook-Template-Python.ipynb) | Template Python | Python |
| [Notebook-Generated](Notebook-Generated.ipynb) | Exemple genere | - |

### Applications

| Notebook | Description | Kernel |
|----------|-------------|--------|
| [Semantic-kernel-AutoInteractive](Semantic-kernel-AutoInteractive.ipynb) | Mode interactif automatise | C# |
| [fort-boyard-csharp](fort-boyard-chsarp.ipynb) | Jeu Fort Boyard | C# |
| [fort-boyard-python](fort-boyard-python.ipynb) | Jeu Fort Boyard | Python |
| [Createur de mail personnaliser](Créateur%20de%20mail%20personnaliser.ipynb) | Generation d'emails | - |

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Kernel** | Point d'entree principal, orchestrateur |
| **Plugins** | Fonctions natives ou semantiques |
| **Planners** | Decomposition de taches complexes |
| **Memory** | Stockage et recherche semantique |
| **Agents** | Entites autonomes avec objectifs |

## Prerequisites

### .NET

```bash
# .NET SDK 8.0+ requis
dotnet --version

# Packages (references dans notebooks)
# - Microsoft.SemanticKernel
# - Microsoft.SemanticKernel.Plugins.Core
```

### Python

```bash
pip install semantic-kernel openai python-dotenv
```

### Configuration

```bash
# Dans GenAI/.env ou Config/settings.json
OPENAI_API_KEY=sk-...
AZURE_OPENAI_ENDPOINT=https://...
AZURE_OPENAI_API_KEY=...
```

## Parcours recommande

```
01-Intro (bases)
    |
02-Advanced (plugins)
    |
03-Agents (autonomie)
    |
04/05-NotebookMaker (meta-programmation)
```

## Ressources

- [Semantic Kernel Documentation](https://learn.microsoft.com/en-us/semantic-kernel/)
- [Semantic Kernel GitHub](https://github.com/microsoft/semantic-kernel)
- [SK Samples](https://github.com/microsoft/semantic-kernel/tree/main/samples)

## Licence

Voir la licence du repository principal.
