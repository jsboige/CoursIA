# SemanticKernel - Microsoft Semantic Kernel

<!-- CATALOG-STATUS
series: GenAI-SemanticKernel
pedagogical_count: 20
breakdown: SemanticKernel=20
maturity: PRODUCTION=12, BETA=3, TEMPLATE=3, ALPHA=2
-->

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Génération de texte](../Texte/README.md)

Microsoft Semantic Kernel représente un tournant dans la manière de construire des applications intelligentes. Ce SDK d'orchestration agentique connecte les LLMs aux outils, données et workflows de votre système. La réponse de Microsoft à l'écosystème LangChain, Semantic Kernel transforme des applications statiques en systèmes autonomes capables de raisonnement, d'apprentissage et d'action.

Cette série pédagogique vous guidera à travers la transition entre le prompt engineering simple et la construction de systèmes multi-agents sophistiqués, où chaque composant travaille de concert pour résoudre des problèmes d'une complexité croissante.

**Fil rouge** : le NotebookMaker, un système à 3 agents (Admin, Coder, Reviewer) qui génère automatiquement des notebooks pédagogiques. Ce démonstrateur incarne l'essence même de Semantic Kernel : orchestrer des agents spécialisés pour résoudre des problèmes complexes.

## Série principale (Python)

Parcours pédagogique complet sur Semantic Kernel en Python :

| # | Notebook | Contenu | Durée |
|---|----------|---------|-------|
| 01 | [SK-1-Fundamentals](01-SemanticKernel-Intro.ipynb) | Kernel, Services, Plugins, Chat | 45 min |
| 02 | [SK-2-Functions](02-SemanticKernel-Advanced.ipynb) | Function Calling moderne, Memory, Groundedness | 50 min |
| 03 | [SK-3-Agents](03-SemanticKernel-Agents.ipynb) | ChatCompletionAgent, AgentGroupChat, OpenAIAssistant | 55 min |
| 04 | [SK-4-Filters](04-SemanticKernel-Filters-Observability.ipynb) | Filtres, Logging, OpenTelemetry | 45 min |
| 05 | [SK-5-VectorStores](05-SemanticKernel-VectorStores.ipynb) | RAG, Embeddings, Qdrant | 50 min |
| 06 | [SK-6-ProcessFramework](06-SemanticKernel-ProcessFramework.ipynb) | Workflows, Orchestration, State | 40 min |
| 07 | [SK-7-MultiModal](07-SemanticKernel-MultiModal.ipynb) | DALL-E, Whisper, GPT-4 Vision | 45 min |
| 08 | [SK-8-MCP](08-SemanticKernel-MCP.ipynb) | Model Context Protocol, Interopérabilité | 45 min |

## Notebooks avancés (Python/C# Interop)

| # | Notebook | Description | Durée |
|---|----------|-------------|-------|
| 09 | [SK-9-Building-CLR](09-SemanticKernel-Building-CLR.ipynb) | Interop Python/C# via pythonnet, chargement DLL .NET | 40 min |
| 10 | [SK-10-NotebookMaker](10-SemanticKernel-NotebookMaker.ipynb) | **Système 3-agents** (Admin, Coder, Reviewer) pour génération de notebooks | 60 min |
| 10a | [SK-10a-NotebookMaker-batch](10a-SemanticKernel-NotebookMaker-batch.ipynb) | Version batch sans UI interactive | 30 min |
| 10b | [SK-10b-NotebookMaker-batch-param](10b-SemanticKernel-NotebookMaker-batch-parameterized.ipynb) | Version paramétrisée pour Papermill | 30 min |

## Démos interactives (curriculum)

Ces notebooks appliquent Semantic Kernel à des cas d'usage concrets. Ils font partie du curriculum (exercices stub inclus), mais sont listés à part car ils ne suivent pas la numérotation principale 01-10.

| Notebook | Langage | Contenu | Exercices |
|----------|---------|---------|-----------|
| [Semantic-kernel-AutoInteractive](Semantic-kernel-AutoInteractive.ipynb) | C# (.NET) | **Conception de notebook assistée** : SK + OpenAI function calling pour générer et exécuter d'autres notebooks .NET interactifs | 3 |
| [Créateur de mail personnalisé](Créateur%20de%20mail%20personnalisé.ipynb) | Python | Workflow multi-agents SK (InputCollector, EmailGenerator) pour la rédaction de courriels | 3 |
| [fort-boyard-csharp](fort-boyard-csharp.ipynb) | C# (.NET) | AgentGroupChat : duel Père Fouras vs Laurent Jalabert (jeu de devinette) | 3 |
| [fort-boyard-python](fort-boyard-python.ipynb) | Python | Contrepartie Python du duel Fort Boyard (KernelFunctionTerminationStrategy) | 3 |

## Templates

| Template | Description |
|----------|-------------|
| [Notebook-Template](Notebook-Template.ipynb) | Template de base C# |
| [Workbook-Template](Workbook-Template.ipynb) | Template workbook C# |
| [Workbook-Template-Python](Workbook-Template-Python.ipynb) | Template Python |

## Artefacts générés (hors curriculum)

> ⚠️ Les notebooks ci-dessous sont des **sorties produites par le système NotebookMaker / AutoInteractive**, pas du curriculum pédagogique. Ils illustrent ce que la chaîne d'agents génère mais ne contiennent pas de parcours d'apprentissage. Ils sont **exclus du compte catalogue pédagogique** (`pedagogical_count`) et ne doivent pas être comptés comme notebooks de la série.

| Fichier | Nature | Origine |
|---------|--------|---------|
| [Notebook-Generated](Notebook-Generated.ipynb) | Scaffold généré (dataset Iris générique) | Output du [NotebookMaker](10-SemanticKernel-NotebookMaker.ipynb) / [AutoInteractive](Semantic-kernel-AutoInteractive.ipynb) |
| `Créateur de mail personnalisé_output.ipynb` | Copie exécutée Papermill | Artefact d'exécution de [Créateur de mail personnalisé](Cr%C3%A9ateur%20de%20mail%20personnalis%C3%A9.ipynb) (suffixe `_output`, non tracké : produit local d'une exécution Papermill) |

Le notebook canonique « Créateur de mail personnalisé » (sans suffixe `_output`) est, lui, un vrai notebook de curriculum (cf. table [Démos interactives](#démos-interactives-curriculum)).

## Concepts clés

| Concept | Description | Notebook |
|---------|-------------|----------|
| **Kernel** | Orchestrateur central | 01 |
| **Services** | Connexions LLM (OpenAI, Azure) | 01 |
| **Plugins** | Collections de fonctions | 01, 02 |
| **Function Calling** | `FunctionChoiceBehavior.Auto()` | 02 |
| **Agents** | Entités autonomes | 03 |
| **AgentGroupChat** | Collaboration multi-agents | 03, 10 |
| **Filters** | Interception avant/après | 04 |
| **Vector Stores** | RAG, embeddings | 05 |
| **Process Framework** | Workflows orchestrés | 06 |
| **Multi-Modal** | Images, audio, vision | 07 |
| **MCP** | Interopérabilité des outils | 08 |
| **pythonnet/CLR** | Interop Python/.NET | 09 |
| **NotebookState** | Gestion état notebook | 10 |
| **SelectionStrategy** | Choix agent dynamique | 10 |

## Parcours recommandé

```text
┌─────────────────────────────────────────────────────────────────────┐
│                     SÉRIE PRINCIPALE (Python)                       │
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
│                     SÉRIE AVANCÉE (Interop)                         │
├─────────────────────────────────────────────────────────────────────┤
│                                              │                      │
│                                              v                      │
│  09-Building-CLR ─────────────────> 10-NotebookMaker                │
│  (Python/C# Interop)                (Agents générateurs)            │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## Prérequis

### Python

```bash
# Environnement recommandé
python -m venv venv
source venv/bin/activate  # Linux/macOS
venv\Scripts\activate     # Windows

# Dépendances
pip install semantic-kernel python-dotenv openai qdrant-client
```

### Configuration

Créer un fichier `.env` dans le répertoire :

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

# Packages (références dans notebooks)
# - Microsoft.SemanticKernel
# - Microsoft.SemanticKernel.Agents.Core
```

## Ressources

- [Semantic Kernel Documentation](https://learn.microsoft.com/en-us/semantic-kernel/)
- [Semantic Kernel GitHub](https://github.com/microsoft/semantic-kernel)
- [SK Blog](https://devblogs.microsoft.com/semantic-kernel/)
- [MCP Specification](https://modelcontextprotocol.io/)

## Recette : construire le NotebookMaker (système 3 agents)

Le fil rouge de cette série est le NotebookMaker, un système multi-agents qui génère automatiquement des notebooks pédagogiques. Voici comment les notebooks s'articulent :

1. **Fondations (01-03)** : [01](01-SemanticKernel-Intro.ipynb) crée un Kernel et connecte un LLM. [02](02-SemanticKernel-Advanced.ipynb) ajoute le function calling et la mémoire. [03](03-SemanticKernel-Agents.ipynb) introduit les agents autonomes et la collaboration via AgentGroupChat.

2. **Observabilité et données (04-06)** : [04](04-SemanticKernel-Filters-Observability.ipynb) intercepte et log les appels. [05](05-SemanticKernel-VectorStores.ipynb) connecte une base vectorielle (RAG). [06](06-SemanticKernel-ProcessFramework.ipynb) orchestre des workflows avec état.

3. **Extensions (07-08)** : [07](07-SemanticKernel-MultiModal.ipynb) ajoute les capacités multimodales (images, audio). [08](08-SemanticKernel-MCP.ipynb) connecte le Kernel au protocole MCP pour l'interopérabilité.

4. **NotebookMaker (09-10)** : [09](09-SemanticKernel-Building-CLR.ipynb) prépare l'interop Python/C#. [10](10-SemanticKernel-NotebookMaker.ipynb) assemble le système 3 agents (Admin, Coder, Reviewer). Les versions [10a](10a-SemanticKernel-NotebookMaker-batch.ipynb) et [10b](10b-SemanticKernel-NotebookMaker-batch-parameterized.ipynb) ajoutent le mode batch et la paramétrisation Papermill.

## Changelog

### Février 2026

- Réorganisation de la série complète (01-10)
- Renumérotation notebooks avancés : 09-Building-CLR, 10-NotebookMaker
- Vérification et validation de tous les notebooks (100% exécution)
- Mise à jour README avec parcours recommandé amélioré

### Janvier 2026

- Modernisation complète de la série Python (8 notebooks)
- Ajout notebooks 04-08 (Filters, VectorStores, Process, MultiModal, MCP)
- Remplacement des Planners dépréciés par `FunctionChoiceBehavior.Auto()`
- Ajout interprétations pédagogiques style GameTheory
- Intégration Qdrant pour Vector Stores

## FAQ

### `semantic-kernel` installé mais `ImportError` au premier notebook

Semantic Kernel évolue rapidement et les versions sont parfois incompatibles entre elles. Si `ImportError: cannot import name 'Kernel'` ou similaire :

```bash
# Vérifier la version installée
pip show semantic-kernel

# Installer la version testée avec les notebooks
pip install semantic-kernel>=1.30.0 python-dotenv openai
```

Les notebooks 01-03 utilisent les APIs stables (`Kernel`, `ChatCompletionAgent`, `AgentGroupChat`). Les APIs dépréciées (`Planner`, `SKContext`) ont été remplacées par `FunctionChoiceBehavior.Auto()` depuis janvier 2026. Si votre code utilise encore `Planner`, consulter le notebook [02](02-SemanticKernel-Advanced.ipynb) pour la migration.

### Le NotebookMaker génère des notebooks vides ou incomplets

Le NotebookMaker (notebook [10](10-SemanticKernel-NotebookMaker.ipynb)) orchestre 3 agents (Admin, Coder, Reviewer) pour générer un notebook. Si le résultat est vide ou incomplet :

- Vérifier que le modèle LLM configuré supporte le function calling (`gpt-4o-mini` minimum, `gpt-4o` recommandé).
- Le système nécessite 3 à 5 itérations agentiques pour converger. Les versions batch ([10a](10a-SemanticKernel-NotebookMaker-batch.ipynb)) et paramétrisée ([10b](10b-SemanticKernel-NotebookMaker-batch-parameterized.ipynb)) offrent plus de contrôle sur le nombre de tours.
- Les filtres d'observabilité (notebook [04](04-SemanticKernel-Filters-Observability.ipynb)) permettent de tracer chaque échange agentique et diagnostiquer les blocages.

### Quelle différence entre Semantic Kernel et LangChain ?

| Critère | Semantic Kernel | LangChain |
|---------|----------------|-----------|
| **Éditeur** | Microsoft | Communautaire |
| **Langues** | Python + C# | Python + JS/TS |
| **Approche** | Plugins et Kernel central | Chains et LCEL |
| **Agents** | `ChatCompletionAgent` + `AgentGroupChat` | `AgentExecutor` |
| **RAG** | VectorStores natifs | Retrievers + VectorStores |
| **Interop .NET** | Natif (pythonnet/CLR) | Non |
| **Maturité entreprise** | Intègre Azure | Écosystème large |

Si vous travaillez dans l'écosystème Microsoft (Azure, .NET, Teams), Semantic Kernel est le choix naturel. Pour un écosystème Python pur ou du prototypage rapide, LangChain offre plus de flexibilité.

### Les agents SK bouclent sans converger

L'`AgentGroupChat` (notebook [03](03-SemanticKernel-Agents.ipynb)) peut entrer en boucle infinie si la `SelectionStrategy` ne définit pas de condition de terminaison claire. Mitigation :

- Utiliser une `TerminationStrategy` explicite (nombre max de tours, mot-clé de fin).
- Limiter `maximum_iterations` dans la configuration du chat.
- La `SelectionStrategy` par défaut est round-robin — pour des agents spécialisés, implémenter une stratégie basée sur le contexte (voir NotebookMaker notebook [10](10-SemanticKernel-NotebookMaker.ipynb)).

### VectorStores / RAG : Qdrant injoignable

Le notebook [05](05-SemanticKernel-VectorStores.ipynb) utilise Qdrant pour le RAG. Si erreur de connexion :

```bash
# Vérifier que Qdrant est actif
curl http://localhost:6333/collections

# Ou utiliser l'instance cloud
QDRANT_URL=https://qdrant.myia.io
QDRANT_API_KEY=votre-cle
```

Le notebook fonctionne en mode démo avec un magasin en mémoire si Qdrant n'est pas disponible. Pour la production, Qdrant (ou un autre store persistant) est recommandé.

### Comment utiliser les filtres pour déboguer les appels LLM ?

Les filtres SK (notebook [04](04-SemanticKernel-Filters-Observability.ipynb)) interceptent chaque appel LLM avant et après exécution. Pour le debug :

```python
from semantic_kernel.filters import FilterTypes

@kernel.filter(FilterTypes.FUNCTION_INVOCATION)
async def log_filter(context, next):
    print(f"Appel: {context.function.name}")
    print(f"Args: {context.arguments}")
    await next(context)
    print(f"Resultat: {context.result}")
```

Ce pattern est essentiel pour comprendre ce que font les agents dans un système multi-agents comme le NotebookMaker.

## Licence

Voir la licence du repository principal.
