# GenAI Texte - Generation de Texte par IA

Ce dossier contient les notebooks dedies a la generation et manipulation de texte avec les LLMs.

## Contenu

| Notebook | Description | Technologies |
|----------|-------------|--------------|
| `1_OpenAI_Intro.ipynb` | Introduction a l'API OpenAI | GPT-4, Chat Completions |
| `2_PromptEngineering.ipynb` | Techniques de prompt engineering | Few-shot, Chain-of-Thought |
| `3_RAG.ipynb` | Retrieval Augmented Generation | Embeddings, Vector Search |
| `4_LocalLlama.ipynb` | Utilisation de LLMs locaux | Llama, Ollama |

## Prerequis

- Cle API OpenAI configuree dans `.env`
- Pour LocalLlama: Ollama installe localement

## Relation avec GenAI Images

Ces notebooks sont complementaires aux modules d'images (00-04).
Ils couvrent la partie "texte" de l'IA generative tandis que les modules
principaux se concentrent sur la generation d'images.

## Parcours suggere

1. `1_OpenAI_Intro` - Bases de l'API
2. `2_PromptEngineering` - Techniques avancees
3. `3_RAG` - Augmentation par recuperation
4. `4_LocalLlama` - Modeles locaux (optionnel)
