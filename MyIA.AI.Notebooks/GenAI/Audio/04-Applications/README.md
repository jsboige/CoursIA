# 04-Applications - Cas d'usage production

[← Audio Orchestration](../03-Orchestration/) | [↑ Audio](../README.md) | [→ Video](../../Video/README.md)

Ce module présente des cas d'usage concrets et des workflows de production pour l'audio génératif.

**Fil rouge podcast** : [04-1](04-1-Educational-Audio-Content.ipynb) automatise la narration de cours. [04-2](04-2-Transcription-Pipeline.ipynb) gère la transcription batch avec sous-titres SRT. [04-3](04-3-Music-Composition-Workflow.ipynb) compose des bandes sonores. [04-4](04-4-Audio-Video-Sync.ipynb) synchronise l'audio avec la vidéo.

**Fil rouge audiobook (Epic #1028)** : [04-6](04-6-Audiobook-Pipeline.ipynb) a [04-12](04-12-Compilation-Audio.ipynb) forment un pipeline agentique 5-pass complet : benchmark des voix, analyse littéraire, casting vocal, annotation prosodique, génération TTS et compilation finale. [04-13](04-13-Audiobook-FishAudio-S2Pro.ipynb) étend le pipeline avec FishAudio S2-Pro, 29 tags prosodiques officiels et validation WER.


## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 14 |
| Kernel | Python 3 |
| Durée estimée | ~8-12h |
| GPU requis | 0-14GB |

## Notebooks

Les sections de cet index sont **thématiques** : deux carnets peuvent y voisiner sans se suivre par le rang. La numérotation `04-NN` fixe l'**ordre de lecture**, et c'est elle que suit le fil de navigation — chaque carnet renvoie à son `NN+1`. L'écart est assumé : `04-18` (transcription note à note) est présenté dans la famille YuE2 dont il partage le service, avant `04-17` (MIR classique), qui vient ensuite comme le socle DSP de cette famille.

### Workflows généraux

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------|
| 1 | [04-1-Educational-Audio-Content](04-1-Educational-Audio-Content.ipynb) | Narration automatique de cours | Mixed | ~10 GB |
| 2 | [04-2-Transcription-Pipeline](04-2-Transcription-Pipeline.ipynb) | Batch transcription, sous-titres SRT | Mixed | ~12 GB |
| 3 | [04-3-Music-Composition-Workflow](04-3-Music-Composition-Workflow.ipynb) | Création musicale multi-étapes | Local GPU | ~14 GB |
| 4 | [04-4-Audio-Video-Sync](04-4-Audio-Video-Sync.ipynb) | Synchronisation audio-video | Mixed | ~10 GB |
| 5 | [04-5-LiveCoding-LLM-Music](04-5-LiveCoding-LLM-Music.ipynb) | Strudel.cc + LLM, live coding musical | OpenAI API | 0 |

### Pipeline Audiobook Agentique (Epic #1028)

Pipeline complet pour générer un audiobook à partir d'un texte littéraire, avec sélection de voix, annotation prosodique et compilation finale.

| # | Notebook | Pass | Contenu | Service | VRAM |
| --- | ---------- | ------ | --------- | --------- | ------ |
| 6 | [04-6-Audiobook-Pipeline](04-6-Audiobook-Pipeline.ipynb) | P0 | Pipeline audiobook orchestrateur | Mixed | ~5 GB |
| 7 | [04-7-TTS-Voice-Benchmark](04-7-TTS-Voice-Benchmark.ipynb) | P0 | Benchmark comparatif des modèles TTS | Kokoro + Qwen3 TTS + OpenAI | ~2 GB |
| 8 | [04-8-Lecture-Analytique](04-8-Lecture-Analytique.ipynb) | P1 | Analyse littéraire, segmentation dialogues/narration | OpenAI API | 0 |
| 9 | [04-9-Voice-Casting](04-9-Voice-Casting.ipynb) | P2 | Attribution de voix par personnage, casting vocal | OpenAI API | 0 |
| 10 | [04-10-Annotation-Prosodique](04-10-Annotation-Prosodique.ipynb) | P3 | Tags prosodiques FishAudio S2-Pro | OpenAI API | 0 |
| 11 | [04-11-Generation-TTS](04-11-Generation-TTS.ipynb) | P4 | Génération audio Kokoro multi-voix | Kokoro TTS | ~2 GB |
| 12 | [04-12-Compilation-Audio](04-12-Compilation-Audio.ipynb) | P5 | Concaténation FFmpeg + normalisation loudness | FFmpeg | 0 |
| 13 | [04-13-Audiobook-FishAudio-S2Pro](04-13-Audiobook-FishAudio-S2Pro.ipynb) | Full | Pipeline v4 FishAudio S2-Pro, 29 tags prosodiques, validation WER | FishAudio + Whisper | ~6 GB |

### Hommage Munkres — musique et mathématiques

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------|
| 14 | [04-14-VoiceLeading-Rendu-GenAI](04-14-VoiceLeading-Rendu-GenAI.ipynb) | Rendu audio intelligent du voice leading App-21 : baseline téléphone vs MusicGen-melody (3 styles H1), spectrogrammes mesurés | MusicGen-melody (GPU local) | ~6 GB |

### Famille YuE2 — compréhension et transcription musicales

Trois satellites : la **compréhension** (MERT2, 04-15), la **génération** ([YuE2, 02-7](../02-Advanced/02-7-YuE2-Song-Generation.ipynb)) et la **transcription** (SheetSage2, 04-16).

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------|
| 15 | [04-15-MERT2-Music-Understanding](04-15-MERT2-Music-Understanding.ipynb) | Embeddings MERT2 (632 M, self-supervised, poids CC BY-NC 4.0) : corpus contrôlé 3 motifs × 4 timbres × 2 transpositions, similarité cosinus, retrieval contexte long FullSong (medley 120 s), sondes linéaires LOO motif vs timbre sur couches L1/L23/L24 | Local GPU (kernel `mert2-gpu`, pins torch 2.6.0 / transformers 4.53.2) | ~4 GB |
| 16 | [04-16-SheetSage2-Audio-To-Score](04-16-SheetSage2-Audio-To-Score.ipynb) | Transcription audio vers partition éditable : SheetSage2 (677 M, base MERT-v2-FullSong + adaptateurs), cinq têtes (mélodie, accords, temps forts, tonalité, structure), artefacts ABC/MIDI/événements horodatés, comparaison à vérité-terrain connue par construction, cycle symbolique→audio→symbolique mesuré | Local GPU (kernel `sheetsage2-gpu`) ; poids CC BY-NC 4.0 (usage commercial interdit) | ~8 GB |

### Transcription note à note — basic-pitch

Là où SheetSage2 (04-16) produit une partition symbolique globale, la **transcription note à note** cherche *quand* chaque note commence, *quelle* hauteur elle porte et *combien de temps* elle dure. basic-pitch (Spotify, ICASSP 2022) est le modèle de référence de cette tâche ; sa variante ONNX tourne sur CPU, ce qui rend le carnet re-exécutable partout.

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------|
| 18 | [04-18-Basic-Pitch-Transcription](04-18-Basic-Pitch-Transcription.ipynb) | Transcription note à note : basic-pitch (ICASSP 2022, ONNX) sur vérité terrain synthétique (11 notes à onsets exacts) et trois accords (9 notes superposées) ; rappel/précision/écart d'onset mesurés, piano-roll vérité vs détection, balayage des seuils du décodeur (onset et frame), trois exercices | CPU local (kernel `basicpitch-t4`, onnxruntime) | 0 (CPU) |

> **Note (consolidation #13741)** : un sibling pédagogique plus minimal (re-voicing CP-SAT + MIDI synthèse, version allégée du canonique) a été archivé sous [`MyIA.AI.Notebooks/GenAI/Audio/_archive/04-14-VoiceLeading-RenduGenAI.ipynb`](../_archive/04-14-VoiceLeading-RenduGenAI.ipynb) pour éliminer le doublon de slot 04-14. Le contenu reste préservé (re-voicing, synthèse MIDI, MusicGen, spectrogrammes, export WAV) ; ce notebook canonique `Rendu-GenAI` (version complète re-exécutée #13398) reste la référence.

### Analyse musicale classique (MIR)

Le socle DSP et statistique sous les approches neuronales de la famille YuE2 : les mêmes questions (tempo, tonalité, accords) traitées par descripteurs et modèles de connaissance compacts, sans entraînement.

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------|
| 17 | [04-17-MIR-Classique](04-17-MIR-Classique.ipynb) | MIR classique librosa : beat tracking + tempo (enveloppe d'onsets, dynamic programming), tonalité Krumhansl–Schmuckler sur chroma CQT, grille d'accords par templates triades — validés sur vérité terrain synthétique (100 BPM, Do majeur, C–Am–F–G) puis vraie musique (exemples librosa brahms/nutcracker), 3 exercices (tempo 140 BPM, tonalité en mode mineur, banque étendue aux accords de septième) | librosa (CPU local) | 0 |

**Flux du pipeline audiobook** :

```text
P0 Benchmark voix → P1 Analyse littéraire → P2 Casting vocal
    → P3 Annotation prosodique → P4 Génération TTS → P5 Compilation finale
```

### Évaluation subjective — protocole MOS

Un rating subjectif n'est interprétable qu'accompagné de son protocole : dans quel ordre présenter les échantillons, comment repérer un auditeur qui note à l'envers du groupe, et quelle incertitude attacher au score. Le carnet ci-dessous importe l'organe `scripts/tts_verification/mos_protocol.py`, lit la rubrique **depuis** `04-7-TTS-Voice-Benchmark` (source de vérité unique), puis exerce l'agrégateur sur une campagne de notes **fictives** : la grille du `04-7` reste vide, c'est l'auditeur qui la remplit. Les proxies automatiques (SNR, SI-SDR, distance log-spectrale, STOI) sont mesurés sur une référence de laboratoire synthétique, pour montrer ce qu'ils capent — et ce qu'ils ne captent pas.

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------|
| 19 | [04-19-Evaluation-MOS](04-19-Evaluation-MOS.ipynb) | Protocole d'écoute subjective (ITU-T P.800) et agrégateur (ITU-R P.808) : lecture de la rubrique depuis le `04-7`, liste d'essais rejouable, fiche de notation pré-remplie, MOS + IC 95 % + rejet des auditeurs aberrants, proxies (SNR, SI-SDR, LSD, STOI) sur référence source-filtre et dégradations maîtrisées, 3 exercices | CPU local (numpy, scipy, torchmetrics, pystoi) | 0 |

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
Texte -> MusicGen -> Édition MIDI -> Voice leading optimal ([App-21 Search](../../../Search/Part3-Cas-pratiques/App-21-VoiceLeading.ipynb)) -> Rendu audio intelligent ([04-14](04-14-VoiceLeading-Rendu-GenAI.ipynb)) -> Post-production -> Export
```

### Audiobook Agentique (Epic #1028)

```text
Texte littéraire -> Benchmark voix (P0)
    -> Segmentation dialogue/narration (P1)
    -> Casting vocal par personnage (P2)
    -> Annotation prosodique [whisper][shout][cold] (P3)
    -> Génération TTS multi-voix Kokoro (P4)
    -> FFmpeg concat + loudnorm (P5)
    -> Audiobook final MP3
```

## Ressources

- [Documentation Audio principale](../README.md)
- [Live Coding Guide](04-5-LiveCoding-LLM-Music.ipynb)
- [GenAI Services Documentation](../../../../docs/genai/genai-services.md)
