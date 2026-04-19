# 03-Orchestration - Multi-modèles & Temps réel

[← Audio Advanced](../02-Advanced/) | [↑ Audio](../README.md) | [→ Audio Applications](../04-Applications/)

Ce module couvre l'orchestration de plusieurs modèles audio, les pipelines complexes, et l'API temps réel d'OpenAI.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 3 |
| Kernel | Python 3 |
| Duree estimee | ~4-6h |
| GPU requis | 0-14GB |

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------|
| 1 | [03-1-Multi-Model-Audio-Comparison](03-1-Multi-Model-Audio-Comparison.ipynb) | Benchmark STT et TTS | Mixed | ~12 GB |
| 2 | [03-2-Audio-Pipeline-Orchestration](03-2-Audio-Pipeline-Orchestration.ipynb) | Pipelines STT→LLM→TTS, podcast | Mixed | ~14 GB |
| 3 | [03-3-Realtime-Voice-API](03-3-Realtime-Voice-API.ipynb) | OpenAI Realtime API, WebSocket | OpenAI API | 0 |

## Prérequis

### API Keys
```bash
# Dans GenAI/.env
OPENAI_API_KEY=sk-...
```

### Dépendences
```bash
pip install -r requirements.txt
pip install -r requirements-audio.txt
pip install websockets  # Pour l'API temps réel
```

## Progression recommandée

1. **03-1-Multi-Model-Audio-Comparison** - Comparatif des modèles pour choisir le bon
2. **03-2-Audio-Pipeline-Orchestration** - Création de pipelines audio complexes
3. **03-3-Realtime-Voice-API** - Intégration temps réel en production

## Concepts clés

### Multi-Model Comparison
- **STT Models** : Whisper API vs Whisper Local vs Chatterbox
- **TTS Models** : OpenAI TTS vs Kokoro vs XTTS vs Chatterbox
- **Métriques** : Latence, qualité, coût, ressources

### Pipeline Orchestration
- **Flow** : Audio → STT → LLM → TTS → Audio
- **Cas d'usage** : Podcast, interview, sous-titrage automatique
- **Optimisation** : Caching, parallélisation, batch processing

### Realtime API
- **WebSocket** : Communication bidirectionnelle
- **Latence** : < 300ms pour une expérience fluide
- **Applications** : Assistant vocal, call center, transcription live

## Architecture

```
STT Input → Processing → LLM Analysis → TTS Output
    ↓           ↓            ↓            ↓
  Whisper    Filtering    GPT-4o    OpenAI TTS
  Local      Enhancement     →       Expressive
```

## Ressources

- [Documentation Audio principale](../README.md)
- [Guide API OpenAI Realtime](https://platform.openai.com/docs/api-reference/realtime)
- [WebSocket Client Documentation](03-3-Realtime-Voice-API.ipynb)