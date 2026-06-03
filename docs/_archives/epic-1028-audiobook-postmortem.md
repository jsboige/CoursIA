# Epic #1028 — Audiobook Agentique Pipeline: Post-Mortem

**Date**: 2026-05-18
**Epic**: #1028
**Source text**: Boule de Suif — Guy de Maupassant
**Resultat**: Pipeline 5-pass complet, 14 segments audio MP3, 5 voix distinctes

---

## Vue d'ensemble

Pipeline agentique de generation d'audiobook a partir d'un texte litteraire. Chaque passe (P0-P5) est un notebook dedie, executable independamment ou en chaine. Le pipeline transforme un texte brut en audiobook multi-voix avec annotation prosodique.

## PRs livrees (8 total)

| PR | Pass | Titre | Merged |
|----|------|-------|--------|
| #1155 | Architecture | Audiobook Pipeline 5-pass agentive architecture | 2026-05-15 |
| #1232 | P0 | TTS voice benchmark | 2026-05-17 |
| #1234 | P1 | Analytical reading + segmentation dialogues/narration | 2026-05-17 |
| #1236 | P2 | Voice casting par personnage | 2026-05-17 |
| #1247 | P3 | Prosodic annotation FishAudio S2-Pro tags | 2026-05-17 |
| #1251 | P4 | TTS generation Kokoro 14 segments | 2026-05-18 |
| #1254 | P5 | Audio compilation FFmpeg + normalisation | OPEN |
| #1258 | Docs | Audio READMEs update | 2026-05-18 |

## Architecture du pipeline

```text
Texte litteraire (Boule de Suif)
    |
P0  [04-7-TTS-Voice-Benchmark]     Benchmark voix Kokoro vs OpenAI
    |   Output: benchmark_report, voix selectionnees
    v
P1  [04-8-Lecture-Analytique]       Analyse litteraire GPT-4o
    |   Output: segments.json (dialogue/narration, speaker, emotion)
    v
P2  [04-9-Voice-Casting]            Attribution voix par personnage
    |   Output: voice_casting_table.csv, echantillons audio
    v
P3  [04-10-Annotation-Prosodique]   Tags expressifs FishAudio
    |   Output: prosodic_annotations.json, book.ssml.md
    v
P4  [04-11-Generation-TTS]          Generation audio Kokoro multi-voix
    |   Output: audiobook_final/ (14 MP3 segments)
    v
P5  [04-12-Compilation-Audio]       FFmpeg concat + loudnorm -16 LUFS
    |   Output: audiobook_final.mp3
    v
Audiobook complet
```

## Donnees de production

- **Segments**: 14 (9 dialogues + 5 narration)
- **Personnages**: 8 (Elisabeth Rousset, Cornudet, Comtesse/Comte de Breville, Carre-Lamadon, Loiseau, 2 soeurs, Narrateur)
- **Voix Kokoro**: `af_sky`, `bm_george`, `af_sarah`, `am_michael`, `bf_isabella`, `bm_lewis`, `bf_emma`
- **Tags prosodiques**: 20 tags sur 14 segments (shout, whisper, cold, timid, onctuous, indignant, pause, slow, laugh)
- **Generation TTS**: 14 fichiers MP3 via Kokoro TTS (port 8191)

## Lecons apprises

### 1. Kokoro TTS retourne du MP3, pas du WAV

Le service Kokoro (Docker port 8191) retourne du MP3 par defaut, pas du WAV. P5 (compilation FFmpeg) doit concatener des MP3 directement, sans conversion intermediaire. Le format WAV n'existe pas dans le pipeline.

### 2. FFmpeg concat + normalisation loudness

La compilation finale utilise `ffmpeg -f concat` + filtre `loudnorm` pour normaliser a -16 LUFS (EBU R128). Les silences entre segments sont inseres via `adelay` ou `apad` pour les pauses prosodiques.

### 3. Catalog drift recurrent

Chaque merge de PR modifie les READMEs et le `COURSE_CATALOG.generated.json`, causant des conflicts et des CI failures "catalog drift" sur les PRs suivantes. Le fix systematique: `generate_catalog.py` + `expand_catalog_markers.py` sur chaque branche avant push. 4 PRs sur 8 ont eu ce probleme.

### 4. Segmentation dialogue/narration : prompt engineering critique

P1 (Lecture Analytique) depend entierement du prompt GPT-4o pour segmenter le texte. La qualite de la segmentation conditionne tout le pipeline en aval. Un prompt trop vague = narrateur assigne aux dialogues, personnages melanges. Le prompt final inclut le texte integral + instructions structurees avec format JSON de sortie.

### 5. Tags prosodiques FishAudio : vocabulaire fixe

FishAudio S2-Pro supporte un vocabulaire fixe de tags expressifs (whisper, shout, cold, timid, laugh, pause, etc.). Le prompt P3 doit generer des tags dans ce vocabulaire uniquement. Tags hors vocabulaire = ignores silencieusement par le TTS.

### 6. Voice casting : Kokoro vs OpenAI

Benchmark P0 a compare les voix Kokoro locales ( gratuites, ~2 GB VRAM) aux voix OpenAI API (payantes, qualite superieure). Pour le pipeline audiobook, Kokoro suffit pour la generation, avec OpenAI comme reference qualite. Le casting final utilise exclusivement Kokoro pour eviter les couts API sur un texte long.

### 7. Pipeline 5-pass : independance vs enchainement

Chaque notebook est autonome (lit ses inputs depuis les fichiers de sortie du pass precedent). Avantage: on peut relancer P3 sans refaire P1-P2. Inconvenient: les chemins de fichiers sont codes en dur dans chaque notebook. Une v2 devrait utiliser un manifeste JSON partage.

### 8. Service Kokoro Docker : pas de streaming

Kokoro TTS ne supporte pas le streaming. Chaque segment est genere en une requete HTTP complete. Pour un texte long (100+ segments), la generation est sequentielle avec un timeout de ~30s par segment. Aucun parallelisme possible sans instance Docker supplementaire.

## Ameliorations futures (v2)

1. **Manifeste JSON partage**: chemin unique pour tous les artefacts inter-passes
2. **Parallelisme P4**: generation TTS en batch avec n instances Kokoro
3. **Streaming audio**: concat live au fur et a mesure de la generation
4. **Support WAV**: option de sortie WAV pour les pipelines professionnels
5. **Clonage vocal XTTS**: utiliser un echantillon vocal personnalise (notebook 02-2) au lieu des voix Kokoro predeterminees
6. **SSML natif**: generer du SSML complet au lieu de tags FishAudio specifiques
7. **Textes longs**: decoupage automatique en chapitres avec separateur audio

## Fichiers cles

| Fichier | Role |
|---------|------|
| `04-Applications/prosodic_output/prosodic_annotations.json` | 14 segments annnotes |
| `04-Applications/prosodic_output/book.ssml.md` | Livre enrichi SSML |
| `04-Applications/voice_casting_output/voice_casting_table.csv` | Tableau casting 8 personnages |
| `04-Applications/audiobook_final/` | 14 MP3 segments + metadata |
| `04-Applications/README.md` | Documentation pipeline |

## Services utilises

| Service | Port | Usage | VRAM |
|---------|------|-------|------|
| Kokoro TTS | 8191 | Generation voix P4 | ~2 GB |
| OpenAI API | -- | Benchmark P0, analyse P1-P3 | 0 |
| FFmpeg | -- | Compilation P5 | 0 |
