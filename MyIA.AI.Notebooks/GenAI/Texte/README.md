# GenAI Texte - Maîtrise des LLMs : Fondement de tout Génératif

<!-- CATALOG-STATUS
series: GenAI-Texte
pedagogical_count: 11
breakdown: Texte=11
maturity: PRODUCTION=10, BETA=1
-->

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Semantic Kernel](../SemanticKernel/README.md)

La maîtrise des LLMs constitue la pierre angulaire de toute expertise en Génératif. Chaque image générée, chaque instruction d'agent et chaque requête RAG trouve son origine dans le texte. Cette série vous guide à travers une progression pédagogique complète pour transformer votre interaction avec l'IA.

## Ce que vous apprendrez

À travers ces 11 notebooks pratiques, vous acquerrez une expertise complète :
- **Art du prompt engineering** : du zéro-shot au chain-of-thought
- **Structuration des réponses** : JSON Schema, Pydantic, extraction de données
- **Intelligence augmentée** : function calling, RAG moderne, code interpreter
- **Raisonnement avancé** : modèles o4-mini, gpt-5-thinking
- **Production enterprise** : gestion de sessions, retry, batch processing
- **Déploiement local** : vLLM, quantification, optimisation des coûts

## Contenu detaille

### Tier 1 : Fondations (Debutant)

| # | Notebook | Description | Duree |
|---|----------|-------------|-------|
| 1 | `1_OpenAI_Intro.ipynb` | Introduction a l'API OpenAI, tokens, Chat Completions, Responses API | 45 min |
| 2 | `2_PromptEngineering.ipynb` | Zero-shot, few-shot, Chain-of-Thought, modeles raisonnants | 50 min |

### Tier 2 : Sorties Structurees (Intermediaire)

| # | Notebook | Description | Duree |
|---|----------|-------------|-------|
| 3 | `3_Structured_Outputs.ipynb` | JSON Schema, Pydantic, mode strict, extraction de donnees | 55 min |
| 4 | `4_Function_Calling.ipynb` | Tools API, appels paralleles, boucle agentique | 60 min |

### Tier 3 : Augmentation (Intermediaire)

| # | Notebook | Description | Duree |
|---|----------|-------------|-------|
| 5 | `5_RAG_Modern.ipynb` | RAG, embeddings, chunking, Responses API multi-turn, citations | 65 min |
| 6 | `6_PDF_Web_Search.ipynb` | Support PDF (base64/file_id), web_search integre | 50 min |
| 7 | `7_Code_Interpreter.ipynb` | Code interpreter, analyse de donnees, generation de graphiques | 55 min |

### Tier 4 : Fonctionnalites Avancees

| # | Notebook | Description | Duree |
|---|----------|-------------|-------|
| 8 | `8_Reasoning_Models.ipynb` | o4-mini, gpt-5-thinking, reasoning_effort, comparaisons | 60 min |
| 9 | `9_Production_Patterns.ipynb` | Conversations API, background mode, retry, batch processing | 70 min |
| 10 | `10_LocalLlama.ipynb` | vLLM, Qwen3.5-35B-A3B, ZwZ-8B, multi-endpoints, benchmarking | 60 min |
| 11 | `11_Quantization.ipynb` | AWQ, GPTQ, llmcompressor, modeles vision, deploiement vLLM | 60 min |

## Prerequis

### Configuration API
1. Copier `.env.example` vers `.env`
2. Ajouter votre cle API OpenAI : `OPENAI_API_KEY=sk-...`

### Pour les notebooks locaux (10)
- Docker avec support GPU
- Ollama ou vLLM installe

## Parcours suggere

```text
┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│  1_OpenAI_Intro ─────► 2_PromptEngineering                     │
│        │                      │                                 │
│        │                      └──────► 8_Reasoning_Models       │
│        │                                                        │
│        └──────► 3_Structured_Outputs                           │
│                       │                                         │
│                       └──────► 4_Function_Calling              │
│                                      │                          │
│                    ┌─────────────────┼─────────────────┐       │
│                    │                 │                 │       │
│                    ▼                 ▼                 ▼       │
│           5_RAG_Modern      7_Code_Interpreter  9_Production   │
│                 │                                              │
│                 └──────► 6_PDF_Web_Search                      │
│                                                                 │
│  10_LocalLlama (independant, prerequis: 1)                     │
│        └──────► 11_Quantization (prerequis: 10)                │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## APIs couvertes

| API | Notebooks | Description |
|-----|-----------|-------------|
| **Chat Completions** | 1-4, 8 | API classique, toujours supportee |
| **Responses API** | 1, 5, 9 | Nouvelle API avec persistence |
| **Embeddings** | 5 | text-embedding-3-large |
| **Tools/Functions** | 4, 6, 7 | Function calling moderne |
| **File Upload** | 6, 7 | Support PDF et fichiers |
| **Reasoning** | 2, 8 | Modeles o4-mini, gpt-5-thinking |

## Technologies et ecosysteme

- **OpenAI API** : GPT-4o, GPT-4o-mini, o4-mini, gpt-5-thinking
- **Python** : openai, pydantic, tiktoken, semantic-kernel
- **Local** : vLLM, Qwen3.5-35B-A3B, ZwZ-8B, llmcompressor, AWQ/GPTQ
- **Bases vectorielles** : scikit-learn (demo), Pinecone, Qdrant, Chroma

## Mode batch

Tous les notebooks supportent un mode batch pour les tests automatises :

```bash
# Dans .env
BATCH_MODE=true
```

Ce mode desactive les interactions utilisateur et utilise des exemples predefinis.

## Validation

```bash
# Valider la structure
python scripts/notebook_tools/notebook_tools.py validate GenAI/Texte --quick

# Executer tous les notebooks
python scripts/notebook_tools/notebook_tools.py execute GenAI/Texte --timeout 300
```

## Recette : maitriser les LLMs pour piloter tout le generatif

Le fil rouge de cette serie est la progression de l'interaction basique avec un LLM vers la maitrise complete en production. Voici comment les tiers s'articulent :

1. **Tier 1** (fondations) : [1_OpenAI_Intro](1_OpenAI_Intro.ipynb) couvre l'API OpenAI et les tokens. [2_PromptEngineering](2_PromptEngineering.ipynb) explore les techniques de prompting (zero-shot, few-shot, chain-of-thought). A la fin, vous savez interagir efficacement avec un LLM.

2. **Tier 2** (sorties structurees) : [3_Structured_Outputs](3_Structured_Outputs.ipynb) maitrise les formats JSON et Pydantic. [4_Function_Calling](4_Function_Calling.ipynb) connecte le LLM a des outils externes. Ces deux notebooks sont essentiels pour tout systeme qui pilote d'autres modeles generatifs (image, audio, video).

3. **Tier 3** (augmentation) : [5_RAG_Modern](5_RAG_Modern.ipynb) et [6_PDF_Web_Search](6_PDF_Web_Search.ipynb) enrichissent le LLM avec des sources externes. [7_Code_Interpreter](7_Code_Interpreter.ipynb) lui donne la capacite d'executer du code.

4. **Tier 4** (production et local) : [8_Reasoning_Models](8_Reasoning_Models.ipynb) exploite les modeles raisonnants. [9_Production_Patterns](9_Production_Patterns.ipynb) couvre les patterns enterprise. [10_LocalLlama](10_LocalLlama.ipynb) et [11_Quantization](11_Quantization.ipynb) deployent en local avec vLLM.

## Cross-series Bridges

| Serie | Lien | Connection |
|-------|------|------------|
| [Image](../Image/README.md) | Prompts structurés | Les textes prompts guident la generation d'images (DALL-E, GPT-5 Image) — notebooks [1](1_OpenAI_Intro.ipynb) et [4](4_Function_Calling.ipynb) |
| [Audio](../Audio/README.md) | STT/TTS + RAG podcast | Whisper STT et TTS APIs sont les bases du pipeline podcast (Audio/03-2) ; le RAG (notebook [5](5_RAG_Modern.ipynb)) alimente le contenu |
| [Video](../Video/README.md) | GPT-5 Video + Sora prompts | La comprehension video (Video/01-2) utilise les memes APIs texte ; Sora (Video/04-3) depend de prompts structures |
| [SemanticKernel](../SemanticKernel/README.md) | Orchestration agentique | Semantic Kernel orchestre les LLMs via plugins et agents — prolonge les patterns de function calling (notebook [4](4_Function_Calling.ipynb)) |
| [SymbolicAI](../../SymbolicAI/README.md) | Reasoning formel | Les modeles raisonnants (notebook [8](8_Reasoning_Models.ipynb)) complementent le reasoning formel (Z3, Tweety, Lean) |

## FAQ

### Chat Completions vs Responses API — laquelle utiliser ?

Les notebooks couvrent les deux APIs OpenAI :

- **Chat Completions** (notebooks 1-4, 8) : l'API classique `client.chat.completions.create()`. Toujours supportee, simple d'usage, stateless. Ideale pour les requetes unitaires et les prototypes.
- **Responses API** (notebooks 1, 5, 9) : la nouvelle API `client.responses.create()`. Ajoute la persistence automatique des conversations, le support natif du RAG multi-turn, et les citations. Recommandee pour les workflows multi-etapes.

En pratique, commencez avec Chat Completions (notebook 1), puis migrez vers Responses API quand vous avez besoin de persistence ou de RAG (notebook 5).

### Structured Outputs echoue en mode strict

Le mode strict (`strict=True`) impose des contraintes sur les schemas JSON :

- **Tous les champs** doivent etre `required` (pas de champ optionnel `Optional`).
- **Pas de types union** complexes (`str | int | None`).
- **Pas de profondeur excessive** (> 5 niveaux d'imbrication).
- Le schema doit etre **deterministe** : chaque champ a exactement un type possible.

Si le mode strict echoue, retirer `strict=True` et utiliser le mode par defaut (moins strict, mais le schema est quand meme respecte dans ~95% des cas). Le notebook [3_Structured_Outputs](3_Structured_Outputs.ipynb) montre les deux approches.

### Function calling : le modele appelle un outil inexistant

Ce phenomene (hallucination d'outils) arrive quand :

- La description de l'outil est ambigue ou incomplete.
- Le prompt utilisateur est vague et le modele "invente" un outil pour repondre.
- Trop d'outils sont declares simultanement (> 10).

Mitigation : fournir des descriptions precises pour chaque outil, valider les arguments cote client avant execution, et limiter le nombre d'outils actifs. Le notebook [4_Function_Calling](4_Function_Calling.ipynb) montre le pattern de validation.

### RAG : les reponses sont hors-sujet ou inventees

Les causes les plus frequentes :

- **Chunking trop grand** : les segments depassent 512 tokens, diluant le contenu pertinent. Utiliser des chunks de 200-400 tokens avec chevauchement de 50 tokens.
- **Embedding inadapte** : `text-embedding-3-small` est plus rapide mais moins precis que `text-embedding-3-large` pour le RAG technique.
- **Pas de citation** : sans verification, le modele peut halluciner des sources. La Responses API (notebook 5) genere automatiquement des citations.
- **Top-k trop eleve** : injecter trop de context noie le signal. Commencer avec `top_k=3` et ajuster.

### Modeles raisonnants (o4-mini, gpt-5-thinking) : tokens et cout

Les modeles raisonnants consomment des **reasoning tokens** (non visibles) en plus des tokens d'entree/sortie. Implications :

- **Cout** : le cout reel peut etre 3-10x superieur a un modele non-raisonnant pour le meme prompt. Utiliser `reasoning_effort="low"` pour les taches simples.
- **Latence** : les modeles raisonnants prennent plus de temps (10-60s vs 2-5s). Pas adaptes au temps reel.
- **Usage** : excellents pour les taches de planification, l'analyse multi-etapes, et la decomposition de problemes complexes. Inutiles pour le simple formatage ou l'extraction.

Le notebook [8_Reasoning_Models](8_Reasoning_Models.ipynb) compare les couts et la qualite entre modeles raisonnants et classiques.

### LLM local (vLLM) : erreur CUDA ou OOM

Les notebooks 10-11 utilisent vLLM pour servir des modeles locaux. Problemes courants :

- **VRAM insuffisante** : Qwen3.5-35B-A3B en FP16 necessite ~70 GB. Utiliser la quantification AWQ (notebook 11) pour reduire a ~12 GB.
- **Version CUDA** : vLLM requiert CUDA 12.1+. Verifier avec `nvidia-smi` et `nvcc --version`.
- **Port deja occupe** : vLLM utilise le port 8000 par defaut. Utiliser `--port 8001` si besoin.
- **Timeout au premier appel** : le chargement du modele prend 30-120s au demarrage. Les appels suivants sont instantanes.

## Ressources

- [OpenAI Documentation](https://platform.openai.com/docs)
- [Responses API](https://platform.openai.com/docs/api-reference/responses)
- [Reasoning Models](https://platform.openai.com/docs/guides/reasoning)
- [Function Calling](https://platform.openai.com/docs/guides/function-calling)
