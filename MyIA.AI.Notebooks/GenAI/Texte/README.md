# GenAI Texte - Generation de Texte par IA

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Semantic Kernel](../SemanticKernel/README.md)

Ce dossier contient une serie complete de notebooks pour maitriser les LLMs et les APIs OpenAI modernes (2025-2026).

## Vue d'ensemble

| Tier | Notebooks | Niveau |
|------|-----------|--------|
| **Fondations** | 1-2 | Debutant |
| **Sorties Structurees** | 3-4 | Intermediaire |
| **Augmentation** | 5-7 | Intermediaire |
| **Avance** | 8-10 | Avance |
| **Validation** | 100% (10/10 notebooks) |

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
| 10 | `10_LocalLlama.ipynb` | vLLM, Ollama, DeepSeek R1, Qwen 2.5, benchmarking local | 60 min |

## Prerequis

### Configuration API
1. Copier `.env.example` vers `.env`
2. Ajouter votre cle API OpenAI : `OPENAI_API_KEY=sk-...`

### Pour les notebooks locaux (10)
- Docker avec support GPU
- Ollama ou vLLM installe

## Parcours suggere

```
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

## Technologies

- **OpenAI API** : GPT-4o, GPT-4o-mini, o4-mini, gpt-5-thinking
- **Python** : openai, pydantic, tiktoken, semantic-kernel
- **Local** : vLLM, Ollama, DeepSeek R1, Qwen 2.5
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
python scripts/notebook_tools.py validate GenAI/Texte --quick

# Executer tous les notebooks
python scripts/notebook_tools.py execute GenAI/Texte --timeout 300
```

## Relation avec les autres series

- **GenAI/Images** : Generation d'images (DALL-E, Stable Diffusion)
- **GenAI/Audio** : Transcription, TTS (Whisper)
- **SymbolicAI** : Reasoning formel (Z3, Tweety, Lean)

## Ressources

- [OpenAI Documentation](https://platform.openai.com/docs)
- [Responses API](https://platform.openai.com/docs/api-reference/responses)
- [Reasoning Models](https://platform.openai.com/docs/guides/reasoning)
- [Function Calling](https://platform.openai.com/docs/guides/function-calling)
