# 01-Foundation - Bases Speech & Audio

[← Documentation Audio](../README.md) | [↑ ..](../README.md) | [→ Audio Advanced](../02-Advanced/)

Ce module couvre les fondamentaux du traitement audio par IA : reconnaissance vocale (STT), synthèse vocale (TTS), et opérations audio de base.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 5 |
| Kernel | Python 3 |
| Duree estimee | ~3-4h |
| GPU requis | 0-10GB |

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------|
| 1 | [01-1-OpenAI-TTS-Intro](01-1-OpenAI-TTS-Intro.ipynb) | API TTS (6 voix, formats, vitesse) | OpenAI API | 0 |
| 2 | [01-2-OpenAI-Whisper-STT](01-2-OpenAI-Whisper-STT.ipynb) | Whisper API + GPT-4o-Transcribe | OpenAI API | 0 |
| 3 | [01-3-Basic-Audio-Operations](01-3-Basic-Audio-Operations.ipynb) | librosa, spectrogrammes, MFCC, pydub | Local | 0 |
| 4 | [01-4-Whisper-Local](01-4-Whisper-Local.ipynb) | Whisper V3 Turbo local, batch | Local GPU | ~10 GB |
| 5 | [01-5-Kokoro-TTS-Local](01-5-Kokoro-TTS-Local.ipynb) | Kokoro 82M, TTS légère | Local GPU | ~2 GB |

## Prérequis

### API Keys
```bash
# Dans GenAI/.env
OPENAI_API_KEY=sk-...
```

### Dépendances
```bash
pip install -r requirements.txt
pip install -r requirements-audio.txt
```

## Progression recommandée

1. **01-1-OpenAI-TTS-Intro** - Introduction à la synthèse vocale avec OpenAI
2. **01-2-OpenAI-Whisper-STT** - Reconnaissance vocale avec Whisper
3. **01-3-Basic-Audio-Operations** - Manipulation audio locale
4. **01-4-Whisper-Local** - Whisper local pour traitement hors ligne
5. **01-5-Kokoro-TTS-Local** - TTS léger sur GPU

## Points clés

- **Cloud vs Local** : Les notebooks 01-1 et 01-2 utilisent l'API OpenAI, 01-3 est local CPU, 01-4 et 01-5 nécessitent un GPU
- **Formats audio** : WAV, MP3, FLAC supportés dans tous les notebooks
- **Qualité** : Whisper V3 Turbo offre meilleure précision que l'API
- **Performance** : Kokoro TTS est optimal pour les systèmes avec peu de VRAM

## Ressources

- [Documentation Audio principale](../README.md)
- [Guide d'installation des dépendances](../../00-GenAI-Environment/README.md)