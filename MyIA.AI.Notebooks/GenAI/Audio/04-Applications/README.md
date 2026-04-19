# 04-Applications - Cas d'usage production

[← Audio Orchestration](../03-Orchestration/) | [↑ Audio](../README.md) | [→ Video](../../Video/README.md)

Ce module présente des cas d'usage concrets et des workflows de production pour l'audio génératif.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 5 |
| Kernel | Python 3 |
| Duree estimee | ~4-6h |
| GPU requis | 0-14GB |

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------|
| 1 | [04-1-Educational-Audio-Content](04-1-Educational-Audio-Content.ipynb) | Narration automatique de cours | Mixed | ~10 GB |
| 2 | [04-2-Transcription-Pipeline](04-2-Transcription-Pipeline.ipynb) | Batch transcription, sous-titres SRT | Mixed | ~12 GB |
| 3 | [04-3-Music-Composition-Workflow](04-3-Music-Composition-Workflow.ipynb) | Création musicale multi-étapes | Local GPU | ~14 GB |
| 4 | [04-4-Audio-Video-Sync](04-4-Audio-Video-Sync.ipynb) | Synchronisation audio-video | Mixed | ~10 GB |
| 5 | [04-5-LiveCoding-LLM-Music](04-5-LiveCoding-LLM-Music.ipynb) | Strudel.cc + LLM, live coding musical | OpenAI API | 0 |

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
pip install moviepy  # Pour synchronisation A/V
pip install strudel  # Pour live coding musical
```

## Cas d'usage

### 04-1 Educational Audio Content
- **Objectif** : Automatiser la narration de contenus pédagogiques
- **Technologies** : TTS + GPT-4o + post-processing
- **Applications** : E-learning, podcasts éducatifs, contenu multilingue

### 04-2 Transcription Pipeline
- **Objectif** : Traitement batch de fichiers audio
- **Technologies** : Whisper STT + post-processing SRT
- **Applications** : Sous-titrage automatique, archives audio, compliance

### 04-3 Music Composition Workflow
- **Objectif** : Workflow de création musicale assistée
- **Technologies** : MusicGen + MIDI + post-production
- **Applications** : Production musicale, sound design, jingles

### 04-4 Audio-Video Sync
- **Objectif** : Synchroniser l'audio et la vidéo automatiquement
- **Technologies** : Audio analysis + video processing
- **Applications** : Dubbing, lip-sync correction, corrections post-production

### 04-5 LiveCoding LLM Music
- **Objectif** : Composition musicale en temps réel avec LLM
- **Technologies** : Strudel.cc + OpenAI API
- **Applications** : Performance live, expérimentation musicale

## Workflows

### Éducation
```
Contenu texte → GPT-4o (structuration) → TTS Narration → Sous-titres → Export
```

### Production Podcast
```
Audio brut → STT → Correction → Enhance → TTS → Podcast final
```

### Musique
```
Texte → MusicGen → Édition MIDI → Post-production → Export
```

## Ressources

- [Documentation Audio principale](../README.md)
- [Live Coding Guide](04-5-LiveCoding-LLM-Music.ipynb)
- [Production Best Practices](../../docs/)