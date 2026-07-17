# CSV de synchro traduction — famille GenAI

**Statut** : Phase 2 rollout (Epic #4957 / #1650). Famille GenAI couverte par l'infrastructure i18n, **une série par CSV** sous `translations/genai/<série>.csv` (layout consolidé canonique).

> **Consolidation (2026-07-17)** : les séries GenAI vivaient auparavant en double — 3 CSV consolidés (`genai/`) + 6 CSV per-series (`genai-<série>/`). Les doublons `finetuning` + `texte` faisaient double-compter le drift (cf `check_translation_sync.py translations`). Le layout est désormais **uniformisé** sous `genai/` : 4 `git mv` (audio/casestudies/image/video) + retrait des 2 doublons (finetuning/texte per-series). Voir #4957.

## Séries couvertes (7 CSV, 3310 cellules)

| Fichier | Série | Notebooks | Cellules | Périmètre fonctionnel |
|---------|-------|-----------|----------|-----------------------|
| [`audio.csv`](audio.csv) | `GenAI/Audio/` (4 sous-niveaux) | 30 | 1128 | Pipeline audio IA : TTS (OpenAI/Kokoro), STT (Whisper API/local), signal (librosa, spectrogrammes, MFCC), orchestration, podcast fil rouge |
| [`casestudies.csv`](casestudies.csv) | `GenAI/CaseStudies/` | 4 | 113 | 4 cas agentiques GenAI : Barbie-Schreck, Fort-Boyard, Medical-Chatbot, Recipe-Maker (Python, services GenAI locaux) |
| [`finetuning.csv`](finetuning.csv) | `GenAI/FineTuning/` | 5 | 161 | QLoRA, SFT, RLHF/DPO, model merging & routing (`FT-01` → `FT-05`) |
| [`image.csv`](image.csv) | `GenAI/Image/` (4 sous-niveaux + `examples/`) | 20 | 533 | Génération d'images : ComfyUI/Forge, SDXL/Flux, ControlNet, inpainting, upscaling, workflows multi-étapes |
| [`posttraining.csv`](posttraining.csv) | `GenAI/PostTraining/` | 7 | 171 | Post-training (`PT_*`) |
| [`texte.csv`](texte.csv) | `GenAI/Texte/` (20 notebooks `1`–`20`) | 20 | 718 | LLMs texte : OpenAI, OWUI, LocalLlama (`1_OpenAI_Intro` → `20_OWUI`) |
| [`video.csv`](video.csv) | `GenAI/Video/` (4 sous-niveaux) | 17 | 486 | Génération vidéo IA (4 sous-niveaux : Foundation, Advanced, Orchestration, Applications) |

**Schéma** : 21 colonnes (#4957 §1). `src_lang=fr`, `src_hash` (sha256-16) + `text_fr` remplies ; colonnes cibles (`text_en`/`es`/`ar`/`fa`/`zh`/`ru`/`pt`) vides en attente du moteur T3 Argumentum (#1650 Phase 1).

**Note owner-lane** : GenAI = famille Python (partition po-2025), sauf SemanticKernel qui a des jumeaux C# .NET. L'extraction i18n est **safe cross-owner** (artefact dérivé = CSV de cellules upstream en lecture seule, pas de modification des notebooks — cf note identique dans `translations/smartcontracts/README.md`).

**Pre-flight secret (obligatoire pour toute série GenAI)** : les notebooks GenAI sont API-heavy (OpenAI, HuggingFace). Avant extraction, scanner les sources de cellules (`sk-*`, `ghp_*`, `hf_*`, `AIza*`, `os.getenv(KEY, "<literal>")`). Les séries ci-dessus sont **safe** : les clés API sont lues via `os.getenv` sans défaut littéral, les seuls défauts sont publics (endpoint API, noms de modèles). Scan gitleaks sur les CSV = 0 hit.

## Régénération

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

```bash
# Depuis la racine du dépôt (exemple pour la série Audio) :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/GenAI/Audio/ \
    --src-lang fr \
    -o translations/genai/audio.csv
```

Adapter le glob `GenAI/<Série>/` et le `-o translations/genai/<série>.csv` par série (audio/casestudies/finetuning/image/posttraining/texte/video).

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/genai/
```

Sortie attendue = JSON `{"anomaly_count": 0}` (IN_SYNC). Les drifts (`SRC_DRIFT`/`TRAD_DRIFT`) apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles.

## Hors scope

- `GenAI/SemanticKernel/` (20 NB SK-1→SK-12, jumeaux C#) — à seeder séparément (twin .NET, collision-check requis).
- `GenAI/RAG-et-Memoire-Semantique/` (1 NB), `GenAI/00-GenAI-Environment/` (6 NB) — candidats futurs.
- `GenAI/<Série>/assets/`, `data/` — supports non pédagogiques (exclus par le glob top-level).

## Voir aussi

- Issue #4957 — design infrastructure + consolidation layout
- Epic #1650 — traduction multilingue du dépôt
- `scripts/translation/README.md` — schéma détaillé
