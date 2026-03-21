# Audio - Speech, Voix & Musique par IA

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Video Workflows](../Video/README.md)

Serie complete de notebooks pour le traitement audio par IA generative : reconnaissance vocale, synthese vocale, clonage de voix, generation musicale et separation de sources.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 19 |
| Sous-dossiers | 4 niveaux |
| Kernel | Python 3 |
| Duree totale | ~12-14h |
| Validation | 100% (19/19 notebooks) |

## Structure

```
Audio/
├── 01-Foundation/     # STT, TTS, bases audio (5 notebooks)
├── 02-Advanced/       # Voice cloning, musique, MIDI, chansons, separation, multi-TTS (7 notebooks)
├── 03-Orchestration/  # Multi-modeles, temps reel (3 notebooks)
└── 04-Applications/   # Education, production, sync A/V (4 notebooks)
```

## Progression par niveau

### 01-Foundation - Bases Speech & Audio

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [01-1-OpenAI-TTS-Intro](01-Foundation/01-1-OpenAI-TTS-Intro.ipynb) | API TTS (6 voix, formats, vitesse) | OpenAI API | 0 |
| [01-2-OpenAI-Whisper-STT](01-Foundation/01-2-OpenAI-Whisper-STT.ipynb) | Whisper API + GPT-4o-Transcribe | OpenAI API | 0 |
| [01-3-Basic-Audio-Operations](01-Foundation/01-3-Basic-Audio-Operations.ipynb) | librosa, spectrogrammes, MFCC, pydub | Local | 0 |
| [01-4-Whisper-Local](01-Foundation/01-4-Whisper-Local.ipynb) | Whisper V3 Turbo local, batch | Local GPU | ~10 GB |
| [01-5-Kokoro-TTS-Local](01-Foundation/01-5-Kokoro-TTS-Local.ipynb) | Kokoro 82M, TTS legere | Local GPU | ~2 GB |

### 02-Advanced - Voix, Musique & Separation

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [02-1-Chatterbox-TTS](02-Advanced/02-1-Chatterbox-TTS.ipynb) | Chatterbox Turbo, emotions, prosodie | Local GPU | ~8 GB |
| [02-2-XTTS-Voice-Cloning](02-Advanced/02-2-XTTS-Voice-Cloning.ipynb) | XTTS v2, clonage vocal zero-shot | Local GPU | ~6 GB |
| [02-3-MusicGen-Generation](02-Advanced/02-3-MusicGen-Generation.ipynb) | Meta MusicGen, text-to-music | Local GPU | ~10 GB |
| [02-4-Demucs-Source-Separation](02-Advanced/02-4-Demucs-Source-Separation.ipynb) | Demucs v4, extraction stems | Local GPU | ~4 GB |
| [02-5-Multi-Model-TTS-Gateway](02-Advanced/02-5-Multi-Model-TTS-Gateway.ipynb) | Gateway multi-TTS (Kokoro, TADA, Qwen3) | tts-api.myia.io | ~12 GB |
| [02-6-MIDI-Generation](02-Advanced/02-6-MIDI-Generation.ipynb) | midi-model (SkyTNT), generation symbolique | Local GPU | ~2-4 GB |
| [02-7-Song-Generation](02-Advanced/02-7-Song-Generation.ipynb) | YuE vs SongGeneration 2, chansons completes | Local GPU | 10-24 GB |
| **OpenAI Realtime API** | 03-3 | `OPENAI_API_KEY` |

## Prerequisites

### API Keys

```bash
# Dans GenAI/.env
OPENAI_API_KEY=sk-...
```

### Dependances Python

```bash
pip install -r requirements.txt
pip install -r requirements-audio.txt
```

### GPU (pour notebooks locaux)

- Minimum : 4 GB VRAM (Demucs, Kokoro)
- Recommande : 10+ GB VRAM (Whisper, MusicGen)
- Optimal : 24 GB VRAM (tous les notebooks)

## Parcours recommande

```
01-Foundation (bases STT/TTS)
    |
02-Advanced (voix, musique)
    |
03-Orchestration (pipelines, temps reel)
    |
04-Applications (production)
    |
Video/ (serie complementaire)
```

| Objectif | Notebooks |
|----------|-----------|
| Decouverte rapide | 01-1, 01-2, 01-3 |
| Speech complet | 01-1 a 02-2 |
| Musique | 02-3, 02-6, 02-7, 02-4, 04-3 |
| Production | Tous + 03 + 04 |

## Licence

Voir la licence du repository principal.
