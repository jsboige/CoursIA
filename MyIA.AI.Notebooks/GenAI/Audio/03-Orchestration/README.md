# 03-Orchestration - Multi-modèles & Temps réel

[← Audio Advanced](../02-Advanced/) | [↑ Audio](../README.md) | [→ Audio Applications](../04-Applications/)

Ce module couvre l'orchestration de plusieurs modèles audio, les pipelines complexes, l'API temps réel d'OpenAI et le streaming TTS local avec pipecat.

**Dans le cadre du fil rouge podcast** : les briques existent, il faut les assembler. [03-1](03-1-Multi-Model-Audio-Comparison.ipynb) compare les modèles STT et TTS pour choisir le meilleur selon le budget et la qualité visés. [03-2](03-2-Audio-Pipeline-Orchestration.ipynb) construit le pipeline STT vers LLM vers TTS qui constitue le coeur du podcast automatisé. [03-3](03-3-Realtime-Voice-API.ipynb) montre l'alternative temps réel d'OpenAI pour les interactions live. [03-4](03-4-TTS-Streaming-Local-Pipecat.ipynb) ajoute la brique locale : du TTS Kokoro servi par le framework d'orchestration pipecat, avec mesures de débit et de latence premier audio.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Kernel | Python 3 |
| Durée estimée | ~5-7h |
| GPU requis | 0-14GB |

Pour un inventaire à jour des carnets, consultez le [catalogue du dépôt](../../../../COURSE_CATALOG.generated.md).

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------|
| 1 | [03-1-Multi-Model-Audio-Comparison](03-1-Multi-Model-Audio-Comparison.ipynb) | Benchmark STT et TTS | Mixed | ~12 GB |
| 2 | [03-2-Audio-Pipeline-Orchestration](03-2-Audio-Pipeline-Orchestration.ipynb) | Pipelines STT→LLM→TTS, podcast | Mixed | ~14 GB |
| 3 | [03-3-Realtime-Voice-API](03-3-Realtime-Voice-API.ipynb) | OpenAI Realtime API, WebSocket | OpenAI API | 0 |
| 4 | [03-4-TTS-Streaming-Local-Pipecat](03-4-TTS-Streaming-Local-Pipecat.ipynb) | TTS Kokoro local, streaming et service pipecat, RTF et TTFA | Local (Kokoro ONNX) | 0 |

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
pip install pipecat-ai kokoro-onnx soundfile  # Pour le TTS streaming local (03-4)
```

## Progression recommandée

1. **03-1-Multi-Model-Audio-Comparison** - Comparatif des modèles pour choisir le bon
2. **03-2-Audio-Pipeline-Orchestration** - Création de pipelines audio complexes
3. **03-3-Realtime-Voice-API** - Intégration temps réel en production
4. **03-4-TTS-Streaming-Local-Pipecat** - TTS local avec mesure du débit et de la latence premier audio

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

### TTS streaming local (pipecat)
- **RTF** : real-time factor, secondes de synthèse par seconde d'audio produit
- **TTFA** : time to first audio, latence avant le premier échantillon en mode streaming
- **Frontière service** : la consommation du générateur `run_tts` du service, sans transport, est le point de mesure fiable hors pipeline complet (comportements pipecat 1.16 mesurés dans le carnet)

## Architecture

```
STT Input → Processing → LLM Analysis → TTS Output
    ↓           ↓            ↓            ↓
  Whisper    Filtering    GPT-4o    OpenAI TTS    |    Kokoro (03-4)
  Local      Enhancement     →       Expressive    |    via pipecat
```

## Ressources

- [Documentation Audio principale](../README.md)
- [Guide API OpenAI Realtime](https://platform.openai.com/docs/api-reference/realtime)
- [WebSocket Client Documentation](03-3-Realtime-Voice-API.ipynb)
- [pipecat - framework d'agents vocaux temps réel](https://docs.pipecat.ai/)
- [Kokoro ONNX - modèle et voix](https://github.com/thewh1teagle/kokoro-onnx)
