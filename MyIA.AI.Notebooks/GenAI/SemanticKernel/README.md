# SemanticKernel - Microsoft Semantic Kernel

Serie de notebooks couvrant Microsoft Semantic Kernel, un SDK pour l'integration de LLMs dans les applications .NET et Python.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks Python | 8 (serie principale 01-08) |
| Notebooks Avances | 4 (interop Python/C# 09-10) |
| Templates | 3 |
| Duree estimee | ~9h (serie complete) |
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

## Notebooks avances (Python/C# Interop)

| # | Notebook | Description | Duree |
|---|----------|-------------|-------|
| 09 | [SK-9-Building-CLR](09-SemanticKernel-Building-CLR.ipynb) | Interop Python/C# via pythonnet, chargement DLL .NET | 40 min |
| 10 | [SK-10-NotebookMaker](10-SemanticKernel-NotebookMaker.ipynb) | **Systeme 3-agents** (Admin, Coder, Reviewer) pour generation de notebooks | 60 min |
| 10a | [SK-10a-NotebookMaker-batch](10a-SemanticKernel-NotebookMaker-batch.ipynb) | Version batch sans UI interactive | 30 min |
| 10b | [SK-10b-NotebookMaker-batch-param](10b-SemanticKernel-NotebookMaker-batch-parameterized.ipynb) | Version parametrisee pour Papermill | 30 min |

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
| **AgentGroupChat** | Collaboration multi-agents | 03, 10 |
| **Filters** | Interception avant/apres | 04 |
| **Vector Stores** | RAG, embeddings | 05 |
| **Process Framework** | Workflows orchestres | 06 |
| **Multi-Modal** | Images, audio, vision | 07 |
| **MCP** | Interoperabilite des outils | 08 |
| **pythonnet/CLR** | Interop Python/.NET | 09 |
| **NotebookState** | Gestion etat notebook | 10 |
| **SelectionStrategy** | Choix agent dynamique | 10 |

## Parcours recommande

```
┌─────────────────────────────────────────────────────────────────────┐
│                     SERIE PRINCIPALE (Python)                       │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  01-Fundamentals ───> 02-Functions ───> 03-Agents                   │
│        │                    │                │                      │
│        v                    v                v                      │
│  04-Filters <────────> 05-VectorStores      │                      │
│        │                    │                │                      │
│        v                    v                │                      │
│  06-ProcessFramework   07-MultiModal         │                      │
│        │                    │                │                      │
│        └──────────> 08-MCP <─┘               │                      │
│                                              │                      │
├─────────────────────────────────────────────────────────────────────┤
│                     SERIE AVANCEE (Interop)                         │
├─────────────────────────────────────────────────────────────────────┤
│                                              │                      │
│                                              v                      │
│  09-Building-CLR ─────────────────> 10-NotebookMaker                │
│  (Python/C# Interop)                (Agents generateurs)            │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
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

### Fevrier 2026

- Reorganisation de la serie complete (01-10)
- Renumerotation notebooks avances : 09-Building-CLR, 10-NotebookMaker
- Verification et validation de tous les notebooks (100% execution)
- Mise a jour README avec parcours recommande ameliore

### Janvier 2026

- Modernisation complete de la serie Python (8 notebooks)
- Ajout notebooks 04-08 (Filters, VectorStores, Process, MultiModal, MCP)
- Remplacement des Planners deprecies par `FunctionChoiceBehavior.Auto()`
- Ajout interpretations pedagogiques style GameTheory
- Integration Qdrant pour Vector Stores

## Licence

Voir la licence du repository principal.
