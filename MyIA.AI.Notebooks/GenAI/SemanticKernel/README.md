# SemanticKernel - Microsoft Semantic Kernel

Serie de notebooks couvrant Microsoft Semantic Kernel, un SDK pour l'integration de LLMs dans les applications .NET et Python.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks Python | 8 (serie principale) |
| Notebooks C# | 7 (avances/templates) |
| Duree estimee | ~6h30 (serie Python) |
| Version SK cible | 1.39+ |

## Serie principale (Python)

Parcours pedagogique complet sur Semantic Kernel en Python :

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 01 | [SK-1-Fundamentals](01-SemanticKernel-Intro.ipynb) | Kernel, Services, Plugins, Chat | 45 min |
| 02 | [SK-2-Functions](02-SemanticKernel-Advanced.ipynb) | Function Calling moderne, Memory, Groundedness | 50 min |
| 03 | [SK-3-Agents](03-SemanticKernel-Agents.ipynb) | ChatCompletionAgent, AgentGroupChat, OpenAIAssistant | 55 min |
| 04 | [SK-4-Filters](04-SemanticKernel-Filters-Observability.ipynb) | Filtres, Logging, OpenTelemetry | 45 min |
| 05 | [SK-5-VectorStores](05-SemanticKernel-VectorStores.ipynb) | RAG, Embeddings, Qdrant | 50 min |
| 06 | [SK-6-ProcessFramework](06-SemanticKernel-ProcessFramework.ipynb) | Workflows, Orchestration, State | 40 min |
| 07 | [SK-7-MultiModal](07-SemanticKernel-MultiModal.ipynb) | DALL-E, Whisper, GPT-4 Vision | 45 min |
| 08 | [SK-8-MCP](08-SemanticKernel-MCP.ipynb) | Model Context Protocol, Interoperabilite | 45 min |

## Notebooks avances (C#/.NET)

| Notebook | Description | Kernel |
|----------|-------------|--------|
| [04-Building Notebooks](04-SemanticKernel-Building%20Notebooks%20with%20clr.ipynb) | Construction de notebooks via CLR | C# |
| [05-NotebookMaker](05-SemanticKernel-NotebookMaker.ipynb) | **Systeme 3-agents** (Admin, Coder, Reviewer) | C# |
| [05-NotebookMaker-batch](05-SemanticKernel-NotebookMaker-batch.ipynb) | Version batch | C# |

## Templates

| Template | Description |
|----------|-------------|
| [Notebook-Template](Notebook-Template.ipynb) | Template de base C# |
| [Workbook-Template](Workbook-Template.ipynb) | Template workbook C# |
| [Workbook-Template-Python](Workbook-Template-Python.ipynb) | Template Python |

## Concepts cles

| Concept | Description | Notebook |
|---------|-------------|----------|
| **Kernel** | Orchestrateur central | 01 |
| **Services** | Connexions LLM (OpenAI, Azure) | 01 |
| **Plugins** | Collections de fonctions | 01, 02 |
| **Function Calling** | `FunctionChoiceBehavior.Auto()` | 02 |
| **Agents** | Entites autonomes | 03 |
| **AgentGroupChat** | Collaboration multi-agents | 03 |
| **Filters** | Interception avant/apres | 04 |
| **Vector Stores** | RAG, embeddings | 05 |
| **Process Framework** | Workflows orchestres | 06 |
| **Multi-Modal** | Images, audio, vision | 07 |
| **MCP** | Interoperabilite des outils | 08 |

## Parcours recommande

```
01-Fundamentals ─────> 02-Functions ─────> 03-Agents
      |                      |                  |
      |                      |                  v
      |                      |         05-NotebookMaker (avance)
      |                      |
      v                      v
04-Filters <────────> 05-VectorStores
      |                      |
      v                      v
06-ProcessFramework   07-MultiModal
      |                      |
      └──────────> 08-MCP <──┘
```

## Prerequisites

### Python

```bash
# Environnement recommande
python -m venv venv
source venv/bin/activate  # Linux/macOS
venv\Scripts\activate     # Windows

# Dependances
pip install semantic-kernel python-dotenv openai qdrant-client
```

### Configuration

Creer un fichier `.env` dans le repertoire :

```bash
OPENAI_API_KEY=sk-...
OPENAI_CHAT_MODEL_ID=gpt-4o-mini

# Optionnel : Qdrant pour notebook 05
QDRANT_URL=https://qdrant.myia.io
QDRANT_API_KEY=...

# Optionnel : Azure OpenAI
AZURE_OPENAI_ENDPOINT=https://...
AZURE_OPENAI_API_KEY=...
```

### .NET (pour notebooks C#)

```bash
# .NET SDK 9.0+ requis
dotnet --version

# Packages (references dans notebooks)
# - Microsoft.SemanticKernel
# - Microsoft.SemanticKernel.Agents.Core
```

## Ressources

- [Semantic Kernel Documentation](https://learn.microsoft.com/en-us/semantic-kernel/)
- [Semantic Kernel GitHub](https://github.com/microsoft/semantic-kernel)
- [SK Blog](https://devblogs.microsoft.com/semantic-kernel/)
- [MCP Specification](https://modelcontextprotocol.io/)

## Changelog

### Janvier 2026

- Modernisation complete de la serie Python (8 notebooks)
- Ajout notebooks 04-08 (Filters, VectorStores, Process, MultiModal, MCP)
- Remplacement des Planners deprecies par `FunctionChoiceBehavior.Auto()`
- Ajout interpretations pedagogiques style GameTheory
- Integration Qdrant pour Vector Stores

## Licence

Voir la licence du repository principal.
