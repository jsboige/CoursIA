# 02-Advanced - Voix, Musique & Séparation

[← Audio Foundation](../01-Foundation/) | [↑ Audio](../README.md) | [→ Audio Orchestration](../03-Orchestration/)

Ce module explore les techniques avancées : clonage vocal, génération musicale, séparation de sources, et modèles TTS expressifs.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 8 |
| Kernel | Python 3 |
| Duree estimee | ~6-8h |
| GPU requis | 2-24GB |

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------|
| 1 | [02-1-Chatterbox-TTS](02-1-Chatterbox-TTS.ipynb) | Chatterbox Turbo, émotions, prosodie | Local GPU | ~8 GB |
| 2 | [02-2-XTTS-Voice-Cloning](02-2-XTTS-Voice-Cloning.ipynb) | XTTS v2, clonage vocal zero-shot | Local GPU | ~6 GB |
| 3 | [02-3-MusicGen-Generation](02-3-MusicGen-Generation.ipynb) | Meta MusicGen, text-to-music | Local GPU | ~10 GB |
| 4 | [02-4-Demucs-Source-Separation](02-4-Demucs-Source-Separation.ipynb) | Demucs v4, extraction stems | Local GPU | ~4 GB |
| 5 | [02-5-Multi-Model-TTS-Gateway](02-5-Multi-Model-TTS-Gateway.ipynb) | Gateway multi-TTS (Kokoro, TADA, Qwen3) | tts-api.myia.io | ~12 GB |
| 6 | [02-6-MIDI-Generation](02-6-MIDI-Generation.ipynb) | midi-model (SkyTNT), génération symbolique | Local GPU | ~2-4 GB |
| 7 | [02-7-Song-Generation](02-7-Song-Generation.ipynb) | YuE vs SongGeneration 2, chansons complètes | Local GPU | 10-24 GB |
| 8 | [02-8-Expressive-TTS](02-8-Expressive-TTS.ipynb) | Fish S2 Pro, Dia TTS, tags expressifs | Local GPU | 6-18 GB |

## Prérequis

### GPU Requirements
- **Minimum** : 4 GB VRAM (Demucs, Kokoro)
- **Recommandé** : 8-12 GB VRAM (XTTS, Chatterbox, MusicGen)
- **Optimal** : 24 GB VRAM (SongGeneration, Expressive TTS)

### Dépendances
```bash
pip install -r requirements.txt
pip install -r requirements-audio.txt
pip install -r requirements-music.txt  # Pour MusicGen, MIDI
```

## Progression recommandée

### Parcours Voix
1. **02-1-Chatterbox-TTS** - TTS avec émotions et prosodie
2. **02-2-XTTS-Voice-Cloning** - Clonage vocal
3. **02-8-Expressive-TTS** - TTS ultra-expressif
4. **02-5-Multi-Model-TTS-Gateway** - Comparatif multi-modèle

### Parcours Musique
1. **02-3-MusicGen-Generation** - Génération de musique textuelle
2. **02-6-MIDI-Generation** - Génération MIDI symbolique
3. **02-7-Song-Generation** - Chansons complètes
4. **02-4-Demucs-Source-Separation** - Séparation de sources

## Technologies clés

| Technologie | Utilisation |
|-------------|-------------|
| **XTTS v2** | Clonage vocal zero-shot |
| **MusicGen** | Génération text-to-music |
| **Demucs v4** | Séparation de sources 4 stems |
| **Chatterbox Turbo** | TTS émotionnel |
| **Fish S2 Pro** | TTS ultra-naturel |

## Cas d'usage

- **Voix IA** : Assistant vocal, doublage, narration personnalisée
- **Musique** : Jingles, bandes sonores, musique algorithmique
- **Production** : Post-traitement audio, remixing, mastering

## Ressources

- [Documentation Audio principale](../README.md)
- [Prérequis techniques](../../00-GenAI-Environment/README.md)