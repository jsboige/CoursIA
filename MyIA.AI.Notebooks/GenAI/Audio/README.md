# Audio - Speech, Voix & Musique par IA

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Video Workflows](../Video/README.md)

Le traitement audio est souvent le parent pauvre de l'IA generative, eclipsé par les images et le texte. Pourtant, la voix et la musique sont les modalites les plus naturelles de l'interaction humaine. Cette serie couvre l'ensemble de la chaine audio IA : reconnaissance vocale, synthese, clonage, generation musicale, et orchestration de pipelines.

29 notebooks repartis sur 4 niveaux progressifs, des bases STT/TTS aux applications de production, dont un pipeline audiobook agentique complet (Epic #1028, livre 18/05/2026, 8 PRs, post-mortem [ici](../../docs/epic-1028-audiobook-postmortem.md)).

## Fil rouge : construire un podcast automatise

L'objectif fil rouge de cette serie est de construire un podcast entierement genere par IA. Chaque niveau apporte une brique supplementaire : TTS pour donner une voix au contenu (niveau 1), clonage vocal et musique pour l'identite sonore (niveau 2), pipelines STT vers LLM vers TTS pour l'assemblage (niveau 3), et workflows de production pour le deploiement (niveau 4).

## Structure

```
Audio/
├── 01-Foundation/     # STT, TTS, bases audio (5 notebooks)
├── 02-Advanced/       # Voice cloning, musique, MIDI, chansons, TTS expressif (9 notebooks)
├── 03-Orchestration/  # Multi-modeles, temps reel (3 notebooks)
└── 04-Applications/   # Education, production, sync A/V, live coding, audiobook (13 notebooks)
```

## Progression par niveau

### 01-Foundation - Bases Speech & Audio

Avant de produire un podcast, il faut maitriser les deux briques de base : la synthese vocale (TTS) pour generer de la parole, et la reconnaissance vocale (STT) pour transcrire des fichiers audio existants. Ce niveau commence par les API cloud (simples et immediates), puis passe en local GPU pour l'autonomie et le controle fin. A la fin de ce niveau, vous savez faire parler une machine et comprendre de la parole.

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [01-1-OpenAI-TTS-Intro](01-Foundation/01-1-OpenAI-TTS-Intro.ipynb) | API TTS (6 voix, formats, vitesse) | OpenAI API | 0 |
| [01-2-OpenAI-Whisper-STT](01-Foundation/01-2-OpenAI-Whisper-STT.ipynb) | Whisper API + GPT-4o-Transcribe | OpenAI API | 0 |
| [01-3-Basic-Audio-Operations](01-Foundation/01-3-Basic-Audio-Operations.ipynb) | librosa, spectrogrammes, MFCC, pydub | Local | 0 |
| [01-4-Whisper-Local](01-Foundation/01-4-Whisper-Local.ipynb) | Whisper V3 Turbo local, batch | Local GPU | ~10 GB |
| [01-5-Kokoro-TTS-Local](01-Foundation/01-5-Kokoro-TTS-Local.ipynb) | Kokoro 82M, TTS legere | Local GPU | ~2 GB |

### 02-Advanced - Voix, Musique & Separation

Un podcast de qualite demande une voix naturelle et une identite sonore distincte. Ce niveau couvre le clonage vocal (creer un narrateur unique a partir d'un echantillon), la generation musicale (jingle et fond sonore), la separation de sources (isoler la voix d'un mix existant), et les modeles TTS expressifs (varier le ton et l'emotion). Deux parcours possibles : voix ou musique, selon l'objectif.

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [02-1-Chatterbox-TTS](02-Advanced/02-1-Chatterbox-TTS.ipynb) | Chatterbox Turbo, emotions, prosodie | Local GPU | ~8 GB |
| [02-2-XTTS-Voice-Cloning](02-Advanced/02-2-XTTS-Voice-Cloning.ipynb) | XTTS v2, clonage vocal zero-shot | Local GPU | ~6 GB |
| [02-3-MusicGen-Generation](02-Advanced/02-3-MusicGen-Generation.ipynb) | Meta MusicGen, text-to-music | Local GPU | ~10 GB |
| [02-4-Demucs-Source-Separation](02-Advanced/02-4-Demucs-Source-Separation.ipynb) | Demucs v4, extraction stems | Local GPU | ~4 GB |
| [02-5-Multi-Model-TTS-Gateway](02-Advanced/02-5-Multi-Model-TTS-Gateway.ipynb) | Gateway multi-TTS (Kokoro, TADA, Qwen3) | tts-api.myia.io | ~12 GB |
| [02-6-MIDI-Generation](02-Advanced/02-6-MIDI-Generation.ipynb) | midi-model (SkyTNT), generation symbolique | Local GPU | ~2-4 GB |
| [02-7-Song-Generation](02-Advanced/02-7-Song-Generation.ipynb) | YuE vs SongGeneration 2, chansons completes | Local GPU | 10-24 GB |
| [02-8-Expressive-TTS](02-Advanced/02-8-Expressive-TTS.ipynb) | Fish S2 Pro, Dia TTS, tags expressifs | Local GPU | 6-18 GB |
| [02-9-AceStep-Music-Generation](02-Advanced/02-9-AceStep-Music-Generation.ipynb) | ACE-Step v1.5, text-to-song multilingue | Local GPU | <4 GB |

### 03-Orchestration - Multi-modeles & Temps reel

Les composants existent, il faut les assembler. Ce niveau construit les pipelines qui transforment un audio en texte (STT), l'enrichissent via un LLM, puis le reconvertissent en parole (TTS). Le notebook 03-2 realise explicitement un pipeline de podcast. L'API Realtime d'OpenAI (03-3) montre la version temps reel pour les interactions live.

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [03-1-Multi-Model-Audio-Comparison](03-Orchestration/03-1-Multi-Model-Audio-Comparison.ipynb) | Benchmark STT et TTS | Mixed | ~12 GB |
| [03-2-Audio-Pipeline-Orchestration](03-Orchestration/03-2-Audio-Pipeline-Orchestration.ipynb) | Pipelines STT->LLM->TTS, podcast | Mixed | ~14 GB |
| [03-3-Realtime-Voice-API](03-Orchestration/03-3-Realtime-Voice-API.ipynb) | OpenAI Realtime API, WebSocket | OpenAI API | 0 |

### 04-Applications - Cas d'usage production

Application directe : les notebooks de ce niveau mettent en oeuvre des workflows complets. 04-1 a 04-5 couvrent la narration de cours, la transcription batch, la composition musicale, la synchronisation audio-video et le live coding. 04-6 a 04-12 forment un pipeline audiobook agentique complet (Epic #1028) : benchmark des voix, analyse litteraire, casting vocal, annotation prosodique, generation TTS et compilation finale.

| Notebook | Contenu | Service | VRAM |
|----------|---------|---------|------|
| [04-1-Educational-Audio-Content](04-Applications/04-1-Educational-Audio-Content.ipynb) | Narration automatique de cours | Mixed | ~10 GB |
| [04-2-Transcription-Pipeline](04-Applications/04-2-Transcription-Pipeline.ipynb) | Batch transcription, sous-titres SRT | Mixed | ~12 GB |
| [04-3-Music-Composition-Workflow](04-Applications/04-3-Music-Composition-Workflow.ipynb) | Creation musicale multi-etapes | Local GPU | ~14 GB |
| [04-4-Audio-Video-Sync](04-Applications/04-4-Audio-Video-Sync.ipynb) | Synchronisation audio-video | Mixed | ~10 GB |
| [04-5-LiveCoding-LLM-Music](04-Applications/04-5-LiveCoding-LLM-Music.ipynb) | Strudel.cc + LLM, live coding musical | OpenAI API | 0 |
| [04-6-Audiobook-Pipeline](04-Applications/04-6-Audiobook-Pipeline.ipynb) | Pipeline audiobook orchestrateur | Mixed | ~10 GB |
| [04-7-TTS-Voice-Benchmark](04-Applications/04-7-TTS-Voice-Benchmark.ipynb) | Benchmark comparatif TTS | Kokoro + OpenAI | ~2 GB |
| [04-8-Lecture-Analytique](04-Applications/04-8-Lecture-Analytique.ipynb) | Analyse litteraire, segmentation | OpenAI API | 0 |
| [04-9-Voice-Casting](04-Applications/04-9-Voice-Casting.ipynb) | Attribution voix par personnage | OpenAI API | 0 |
| [04-10-Annotation-Prosodique](04-Applications/04-10-Annotation-Prosodique.ipynb) | Tags prosodiques FishAudio S2-Pro | OpenAI API | 0 |
| [04-11-Generation-TTS](04-Applications/04-11-Generation-TTS.ipynb) | Generation TTS multi-voix Kokoro | Kokoro TTS | ~2 GB |
| [04-12-Compilation-Audio](04-Applications/04-12-Compilation-Audio.ipynb) | FFmpeg concat + normalisation | FFmpeg | 0 |
| [04-13-Audiobook-FishAudio-S2Pro](04-Applications/04-13-Audiobook-FishAudio-S2Pro.ipynb) | Pipeline v4 FishAudio S2-Pro, 29 tags prosodiques, validation WER | FishAudio + Whisper | ~2 GB |

## Technologies

| Technologie | Notebooks | Prerequis |
|-------------|-----------|-----------|
| **OpenAI TTS/STT** | 01-1, 01-2 | `OPENAI_API_KEY` |
| **Whisper V3 Turbo** | 01-4 | GPU ~10 GB VRAM |
| **Kokoro TTS** | 01-5, 04-11 | GPU ~2 GB VRAM |
| **Chatterbox Turbo** | 02-1 | GPU ~8 GB VRAM |
| **XTTS v2** | 02-2 | GPU ~6 GB VRAM |
| **MusicGen (Meta)** | 02-3 | GPU ~10 GB VRAM |
| **Demucs v4 (Meta)** | 02-4 | GPU ~4 GB VRAM |
| **Multi-TTS Gateway** | 02-5 | `TTS_API_URL` (tts-api.myia.io) |
| **midi-model (SkyTNT)** | 02-6 | GPU ~2 GB VRAM, FluidSynth |
| **YuE / SongGeneration 2** | 02-7 | GPU 10-24 GB VRAM |
| **Fish S2 Pro / Dia TTS** | 02-8 | GPU 6-18 GB VRAM |
| **OpenAI Realtime API** | 03-3 | `OPENAI_API_KEY` |
| **FFmpeg** | 04-12 | Installe systeme |

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

## Recette : construire un podcast automatise

Le fil rouge de cette serie est la creation d'un podcast genere par IA. Voici comment les niveaux s'articulent pour y parvenir :

1. **01-Foundation** (TTS + STT) : [01-1](01-Foundation/01-1-OpenAI-TTS-Intro.ipynb) et [01-5](01-Foundation/01-5-Kokoro-TTS-Local.ipynb) vous donnent les bases de la synthese vocale. [01-2](01-Foundation/01-2-OpenAI-Whisper-STT.ipynb) et [01-4](01-Foundation/01-4-Whisper-Local.ipynb) couvrent la reconnaissance vocale. A la fin de ce niveau, vous savez transformer du texte en audio et inversement.

2. **02-Advanced** (voix + musique) : [02-2](02-Advanced/02-2-XTTS-Voice-Cloning.ipynb) clone une voix pour creer un narrateur coherent. [02-3](02-Advanced/02-3-MusicGen-Generation.ipynb) genere le jingle et le fond sonore. [02-4](02-Advanced/02-4-Demucs-Source-Separation.ipynb) isole les pistes si besoin, et [02-8](02-Advanced/02-8-Expressive-TTS.ipynb) ajoute de l'expressivite.

3. **03-Orchestration** (assemblage) : [03-1](03-Orchestration/03-1-Multi-Model-Audio-Comparison.ipynb) compare les modeaux pour choisir le meilleur STT/TTS selon le budget. [03-2](03-Orchestration/03-2-Audio-Pipeline-Orchestration.ipynb) assemble le pipeline STT vers LLM vers TTS qui constitue le coeur du podcast automatise.

4. **04-Applications** (production) : [04-1](04-Applications/04-1-Educational-Audio-Content.ipynb) applique le pipeline a la narration de cours. [04-2](04-Applications/04-2-Transcription-Pipeline.ipynb) gere la transcription batch pour les episodes longs. [04-4](04-Applications/04-4-Audio-Video-Sync.ipynb) synchronise avec la piste video si le podcast a une composante visuelle.

## Licence

Voir la licence du repository principal.
