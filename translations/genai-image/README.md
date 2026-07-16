# CSV de synchro traduction — série GenAI/Image

**Statut** : Phase 0.5 backfill (Epic #4957 / #1650). Série GenAI/Image couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`genai-image.csv`](genai-image.csv) | `GenAI/Image/` (4 sous-niveaux : 01-Foundation, 02-Advanced, 03-Orchestration, 04-Applications + `examples/`) | 20 | 533 (21 colonnes) |

**Note owner-lane** : l'extraction i18n est **safe owner-lane** (artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks).

**Périmètre fonctionnel** : la série couvre la génération d'images par IA — fondamentaux (ComfyUI, Forge, pipelines SDXL/Flux), techniques avancées (ControlNet, inpainting, upscaling), orchestration (workflows multi-étapes, API) et applications (cas d'usage pédagogiques). Le sous-dossier `examples/` (3 notebooks) contient des démos cross-domaine (histoire-géographie, littérature, sciences).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/GenAI/Image/ \
    --src-lang fr \
    -o translations/genai-image/genai-image.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/genai-image/
```

Sortie attendue = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Voir aussi

- Issue #4957 — design infrastructure
- Epic #1650 — traduction multilingue du dépôt
- `scripts/translation/README.md` — schéma détaillé
