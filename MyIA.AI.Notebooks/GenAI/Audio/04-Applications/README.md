# 04-Applications - Cas d'usage production

[← Audio Orchestration](../03-Orchestration/) | [↑ Audio](../README.md) | [→ Video](../../Video/README.md)

Ce module presente des cas d'usage concrets et des workflows de production pour l'audio generatif.

**Fil rouge podcast** : [04-1](04-1-Educational-Audio-Content.ipynb) automatise la narration de cours. [04-2](04-2-Transcription-Pipeline.ipynb) gere la transcription batch avec sous-titres SRT. [04-3](04-3-Music-Composition-Workflow.ipynb) compose des bandes sonores. [04-4](04-4-Audio-Video-Sync.ipynb) synchronise l'audio avec la video.

**Fil rouge audiobook (Epic #1028)** : [04-6](04-6-Audiobook-Pipeline.ipynb) a [04-12](04-12-Compilation-Audio_output.ipynb) forment un pipeline agentique 5-pass complet : benchmark des voix, analyse litteraire, casting vocal, annotation prosodique, generation TTS et compilation finale.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 12 |
| Kernel | Python 3 |
| Duree estimee | ~8-12h |
| GPU requis | 0-14GB |

## Notebooks

### Workflows generaux

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------|
| 1 | [04-1-Educational-Audio-Content](04-1-Educational-Audio-Content.ipynb) | Narration automatique de cours | Mixed | ~10 GB |
| 2 | [04-2-Transcription-Pipeline](04-2-Transcription-Pipeline.ipynb) | Batch transcription, sous-titres SRT | Mixed | ~12 GB |
| 3 | [04-3-Music-Composition-Workflow](04-3-Music-Composition-Workflow.ipynb) | Creation musicale multi-etapes | Local GPU | ~14 GB |
| 4 | [04-4-Audio-Video-Sync](04-4-Audio-Video-Sync.ipynb) | Synchronisation audio-video | Mixed | ~10 GB |
| 5 | [04-5-LiveCoding-LLM-Music](04-5-LiveCoding-LLM-Music.ipynb) | Strudel.cc + LLM, live coding musical | OpenAI API | 0 |

### Pipeline Audiobook Agentique (Epic #1028)

Pipeline complet de 7 notebooks pour generer un audiobook a partir d'un texte litteraire, avec selection de voix, annotation prosodique et compilation finale.

| # | Notebook | Pass | Contenu | Service | VRAM |
| --- | ---------- | ------ | --------- | --------- | ------ |
| 6 | [04-6-Audiobook-Pipeline](04-6-Audiobook-Pipeline.ipynb) | P0 | Pipeline audiobook orchestrateur | Mixed | ~10 GB |
| 7 | [04-7-TTS-Voice-Benchmark](04-7-TTS-Voice-Benchmark.ipynb) | P0 | Benchmark comparatif des modeles TTS | Kokoro + OpenAI | ~2 GB |
| 8 | [04-8-Lecture-Analytique](04-8-Lecture-Analytique.ipynb) | P1 | Analyse litteraire, segmentation dialogues/narration | OpenAI API | 0 |
| 9 | [04-9-Voice-Casting](04-9-Voice-Casting.ipynb) | P2 | Attribution de voix par personnage, casting vocal | OpenAI API | 0 |
| 10 | [04-10-Annotation-Prosodique](04-10-Annotation-Prosodique.ipynb) | P3 | Tags prosodiques FishAudio S2-Pro | OpenAI API | 0 |
| 11 | [04-11-Generation-TTS](04-11-Generation-TTS_output.ipynb) | P4 | Generation audio Kokoro multi-voix | Kokoro TTS | ~2 GB |
| 12 | [04-12-Compilation-Audio](04-12-Compilation-Audio_output.ipynb) | P5 | Concatenation FFmpeg + normalisation loudness | FFmpeg | 0 |

**Flux du pipeline audiobook** :

```text
P0 Benchmark voix → P1 Analyse litteraire → P2 Casting vocal
    → P3 Annotation prosodique → P4 Generation TTS → P5 Compilation finale
```

## Prerequis

### API Keys
```bash
# Dans GenAI/.env
OPENAI_API_KEY=sk-...
```

### Dependances
```bash
pip install -r requirements.txt
pip install -r requirements-audio.txt
pip install moviepy  # Pour synchronisation A/V
pip install strudel  # Pour live coding musical
pip install pydub    # Pour manipulation audio
# FFmpeg requis pour 04-12 (compilation audio)
```

## Workflows

### Education

```text
Contenu texte -> GPT-4o (structuration) -> TTS Narration -> Sous-titres -> Export
```

### Production Podcast

```text
Audio brut -> STT -> Correction -> Enhance -> TTS -> Podcast final
```

### Musique

```text
Texte -> MusicGen -> Edition MIDI -> Post-production -> Export
```

### Audiobook Agentique (Epic #1028)

```text
Texte litteraire -> Benchmark voix (P0)
    -> Segmentation dialogue/narration (P1)
    -> Casting vocal par personnage (P2)
    -> Annotation prosodique [whisper][shout][cold] (P3)
    -> Generation TTS multi-voix Kokoro (P4)
    -> FFmpeg concat + loudnorm (P5)
    -> Audiobook final MP3
```

## Ressources

- [Documentation Audio principale](../README.md)
- [Live Coding Guide](04-5-LiveCoding-LLM-Music.ipynb)
- [Production Best Practices](../../docs/)