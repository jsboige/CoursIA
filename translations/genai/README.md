# CSV de synchro traduction — famille GenAI

**Statut** : Phase 2 rollout (Epic #4957 / #1650). Famille GenAI couverte par l'infrastructure i18n, une série par CSV (atomic scope).

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`finetuning.csv`](finetuning.csv) | `GenAI/FineTuning/` | 5 (`FT-01-Introduction-FineTuning` → `FT-05-ModelMerging-Routing`, Python — QLoRA, SFT, RLHF/DPO, model merging & routing) | 161 (markdown + code, 20 colonnes) |

**Schéma** : 20 colonnes (#4957 §1). `src_lang=fr`, `src_hash` (sha256-16) + `text_fr` remplies ; colonnes cibles (`text_en/es/ar/...`) vides pour le moteur T3 Argumentum (#1650 Phase 1).

**Séries GenAI futures (candidats non couverts)** : `GenAI/SemanticKernel/` (20 NB SK-1→SK-12), `GenAI/Texte/` (20 NB 1_OpenAI_Intro → 20_OWUI), `GenAI/PostTraining/` (7 NB `PT_*`), `GenAI/RAG-et-Memoire-Semantique/` (1 NB), `GenAI/00-GenAI-Environment/` (6 NB). À seeder une série par CSV après collision-check + FR-first check + secret pre-flight.

**Pre-flight secret (obligatoire pour toute série GenAI)** : les notebooks GenAI sont API-heavy (OpenAI, HuggingFace). Avant extraction, scanner les sources de cellules (`sk-*`, `ghp_*`, `hf_*`, `AIza*`, `os.getenv(KEY, "<literal>")`). Les notebooks FT-* sont **safe** : les clés API sont lues via `os.getenv` sans défaut littéral, les seuls défauts sont publics (endpoint API, noms de modèles). Scan gitleaks sur le CSV = 0 hit. Si une série contient un défaut `sk-...`/`hf_...` littéral, le CSV le prendrait verbatim = bloquer avant extraction.

**Note owner-floue** : GenAI = famille Python (partition po-2025), sauf SemanticKernel qui a des jumeaux C# .NET. L'extraction i18n est **safe cross-owner** (artefact dérivé = CSV de cellules upstream en lecture seule, pas de modification des notebooks — cf note identique dans `translations/smartcontracts/README.md`).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/GenAI/FineTuning/FT-*.ipynb \
    -o translations/genai/finetuning.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/genai/finetuning.csv
```

## Hors scope

- `GenAI/Image/`, `GenAI/Audio/`, `GenAI/Video/` — séries distinctes (assets binaires lourds, à seeder séparément après vérification FR-first).
- `GenAI/FineTuning/assets/`, `data/` — supports non pédagogiques (exclus par le glob `FT-*.ipynb` top-level).
