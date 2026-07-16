# CSV de synchro traduction — série GenAI/Texte

**Statut** : Phase 0.5 backfill (Epic #4957 / #1650). Série GenAI/Texte couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`genai-texte.csv`](genai-texte.csv) | `GenAI/Texte/` (20 notebooks à plat, numérotés 1–20) | 20 | 718 (21 colonnes) |

**Note owner-lane** : l'extraction i18n est **safe owner-lane** (artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks).

**Périmètre fonctionnel** : la série couvre les LLMs texte de bout en bout — fondamentaux API (intro OpenAI, prompt engineering, structured outputs, function calling), techniques modernes (RAG, recherche PDF/Web, code interpreter, reasoning models, patterns de production), puis servitude et orchestration locale (LLMs locaux avec llama.cpp/Ollama, quantization, scaling test-time, agentic orchestration, mémoire persistante, Tree of Thoughts, plugins Semantic Kernel, orchestration Open WebUI native et API). Clôture la **coverage media-family GenAI** (Audio/Image/Video/Texte).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/GenAI/Texte/ \
    --src-lang fr \
    -o translations/genai-texte/genai-texte.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/genai-texte/
```

Sortie attendue = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Voir aussi

- Issue #4957 — design infrastructure
- Epic #1650 — traduction multilingue du dépôt
- `scripts/translation/README.md` — schéma détaillé
