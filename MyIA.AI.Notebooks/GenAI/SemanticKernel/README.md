# SemanticKernel - Microsoft Semantic Kernel

<!-- CATALOG-STATUS
series: GenAI-SemanticKernel
pedagogical_count: 20
breakdown: SemanticKernel=20
maturity: PRODUCTION=12, BETA=3, TEMPLATE=3, ALPHA=2
-->

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

## FAQ

### `semantic-kernel` installe mais `ImportError` au premier notebook

Semantic Kernel evolue rapidement et les versions sont parfois incompatibles entre elles. Si `ImportError: cannot import name 'Kernel'` ou similaire :

```bash
# Verifier la version installee
pip show semantic-kernel

# Installer la version testee avec les notebooks
pip install semantic-kernel>=1.30.0 python-dotenv openai
```

Les notebooks 01-03 utilisent les APIs stables (`Kernel`, `ChatCompletionAgent`, `AgentGroupChat`). Les APIs depreciees (`Planner`, `SKContext`) ont ete remplacees par `FunctionChoiceBehavior.Auto()` depuis janvier 2026. Si votre code utilise encore `Planner`, consulter le notebook [02](02-SemanticKernel-Advanced.ipynb) pour la migration.

### Le NotebookMaker genere des notebooks vides ou incomplets

Le NotebookMaker (notebook [10](10-SemanticKernel-NotebookMaker.ipynb)) orchestre 3 agents (Admin, Coder, Reviewer) pour generer un notebook. Si le resultat est vide ou incomplet :

- Verifier que le model LLM configure supporte le function calling (`gpt-4o-mini` minimum, `gpt-4o` recommande).
- Le systeme necessite 3 a 5 iterations agentiques pour converger. Les versions batch ([10a](10a-SemanticKernel-NotebookMaker-batch.ipynb)) et parametrisee ([10b](10b-SemanticKernel-NotebookMaker-batch-parameterized.ipynb)) offrent plus de controle sur le nombre de tours.
- Les filtres d'observabilite (notebook [04](04-SemanticKernel-Filters-Observability.ipynb)) permettent de tracer chaque echange agentique et diagnostiquer les blocages.

### Quelle difference entre Semantic Kernel et LangChain ?

| Critere | Semantic Kernel | LangChain |
|---------|----------------|-----------|
| **Editeur** | Microsoft | Communautaire |
| **Langues** | Python + C# | Python + JS/TS |
| **Approche** | Plugins et Kernel central | Chains et LCEL |
| **Agents** | `ChatCompletionAgent` + `AgentGroupChat` | `AgentExecutor` |
| **RAG** | VectorStores natifs | Retrievers + VectorStores |
| **Interop .NET** | Natif (pythonnet/CLR) | Non |
| **Maturite entreprise** | Integre Azure | Ecosysteme large |

Si vous travaillez dans l'ecosysteme Microsoft (Azure, .NET, Teams), Semantic Kernel est le choix naturel. Pour un ecosysteme Python pur ou du prototypage rapide, LangChain offre plus de flexibilite.

### Les agents SK bouclent sans converger

L'`AgentGroupChat` (notebook [03](03-SemanticKernel-Agents.ipynb)) peut entrer en boucle infinie si la `SelectionStrategy` ne definit pas de condition de terminaison claire. Mitigation :

- Utiliser une `TerminationStrategy` explicite (nombre max de tours, mot-cle de fin).
- Limiter `maximum_iterations` dans la configuration du chat.
- La `SelectionStrategy` par defaut est round-robin — pour des agents specialises, implementer une strategie basee sur le contexte (voir NotebookMaker notebook [10](10-SemanticKernel-NotebookMaker.ipynb)).

### VectorStores / RAG : Qdrant injoignable

Le notebook [05](05-SemanticKernel-VectorStores.ipynb) utilise Qdrant pour le RAG. Si erreur de connexion :

```bash
# Verifier que Qdrant est actif
curl http://localhost:6333/collections

# Ou utiliser l'instance cloud
QDRANT_URL=https://qdrant.myia.io
QDRANT_API_KEY=votre-cle
```

Le notebook fonctionne en mode demo avec un magasin en memoire si Qdrant n'est pas disponible. Pour la production, Qdrant (ou un autre store persistant) est recommande.

### Comment utiliser les filtres pour deboguer les appels LLM ?

Les filtres SK (notebook [04](04-SemanticKernel-Filters-Observability.ipynb)) interceptent chaque appel LLM avant et apres execution. Pour le debug :

```python
from semantic_kernel.filters import FilterTypes

@kernel.filter(FilterTypes.FUNCTION_INVOCATION)
async def log_filter(context, next):
    print(f"Appel: {context.function.name}")
    print(f"Args: {context.arguments}")
    await next(context)
    print(f"Resultat: {context.result}")
```

Ce pattern est essentielle pour comprendre ce que font les agents dans un systeme multi-agents comme le NotebookMaker.

## Licence

Voir la licence du repository principal.
