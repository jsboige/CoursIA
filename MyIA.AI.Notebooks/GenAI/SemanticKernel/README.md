# SemanticKernel - Microsoft Semantic Kernel

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Text Generation](../Texte/README.md)

Microsoft Semantic Kernel represente un tournant dans la maniere de construire des applications intelligentes. Ce SDK d'orchestration agentique connecte les LLMs aux outils, donnees et workflows de votre systeme. La reponse de Microsoft a l'ecosysteme LangChain, Semantic Kernel transforme des applications statiques en systemes autonomes capables de raisonnement, d'apprentissage et d'action.

Cette serie pedagogique vous guidera a travers la transition entre le prompt engineering simple et la construction de systemes multi-agents sophistiques, ou chaque composant travaille de concert pour resoudre des problemes d'une complexite croissante.

**Fil rouge** : le NotebookMaker, un systeme a 3 agents (Admin, Coder, Reviewer) qui genere automatiquement des notebooks pedagogiques. Ce demonstrateur incarne l'essence meme de Semantic Kernel : orchestrer des agents specialises pour resoudre des problemes complexes.

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

```text
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
OPENAI_CHAT_MODEL_ID=qwen3.6-35b-a3b

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

## Recette : construire le NotebookMaker (systeme 3 agents)

Le fil rouge de cette serie est le NotebookMaker, un systeme multi-agents qui genere automatiquement des notebooks pedagogiques. Voici comment les notebooks s'articulent :

1. **Fondations (01-03)** : [01](01-SemanticKernel-Intro.ipynb) cree un Kernel et connecte un LLM. [02](02-SemanticKernel-Advanced.ipynb) ajoute le function calling et la memoire. [03](03-SemanticKernel-Agents.ipynb) introduit les agents autonomes et la collaboration via AgentGroupChat.

2. **Observabilite et donnees (04-06)** : [04](04-SemanticKernel-Filters-Observability.ipynb) intercepte et log les appels. [05](05-SemanticKernel-VectorStores.ipynb) connecte une base vectorielle (RAG). [06](06-SemanticKernel-ProcessFramework.ipynb) orchestre des workflows avec etat.

3. **Extensions (07-08)** : [07](07-SemanticKernel-MultiModal.ipynb) ajoute les capacites multimodales (images, audio). [08](08-SemanticKernel-MCP.ipynb) connecte le Kernel au protocole MCP pour l'interopabilite.

4. **NotebookMaker (09-10)** : [09](09-SemanticKernel-Building-CLR.ipynb) prepare l'interop Python/C#. [10](10-SemanticKernel-NotebookMaker.ipynb) assemble le systeme 3 agents (Admin, Coder, Reviewer). Les versions [10a](10a-SemanticKernel-NotebookMaker-batch.ipynb) et [10b](10b-SemanticKernel-NotebookMaker-batch-parameterized.ipynb) ajoutent le mode batch et la parametrisation Papermill.

## Cross-series Bridges

| Serie | Lien | Connection |
|-------|------|-------------|
| [GenAI/Texte](../Texte/README.md) | LLMs et APIs | Les notebooks Texte couvrent les memes modeles (OpenAI, Anthropic) que SemanticKernel les orchestre en agents |
| [GenAI/Image](../Image/README.md) | Generation d'images | Le notebook 07-MultiModal utilise la generation d'images DALL-E via le Kernel SK |
| [GenAI/Audio](../Audio/README.md) | Speech et TTS | Le notebook 07-MultiModal integre aussi le TTS (text-to-speech) via le Kernel |
| [ML](../../ML/README.md) | Pipelines ML | Le NotebookMaker (10) genere des notebooks ML automatiquement, la validation croisee ML-4 evalue les modeles produits |
| [QuantConnect](../../QuantConnect/README.md) | Trading algorithmique | Les agents SK peuvent etre connectes a des sources de donnees financieres via MCP (08) pour des signaux de trading LLM-augmentes |
| [Vibe-Coding](../Vibe-Coding/README.md) | Developpement avec agents | Les patterns d'orchestration multi-agents du NotebookMaker (10) s'appliquent aux workflows Vibe-Coding |

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
