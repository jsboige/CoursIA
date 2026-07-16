# CSV de synchro traduction — série GenAI/Video

**Statut** : Phase 0.5 backfill (Epic #4957 / #1650). Série GenAI/Video couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`genai-video.csv`](genai-video.csv) | `GenAI/Video/` (4 sous-niveaux : 01-Foundation, 02-Advanced, 03-Orchestration, 04-Applications) | 17 | 486 (21 colonnes) |

**Note owner-lane** : l'extraction i18n est **safe owner-lane** (artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks).

**Périmètre fonctionnel** : la série couvre la génération vidéo par IA — fondamentaux (text-to-video, image-to-video, modèles Wan/Kling/Hunyuan), techniques avancées (interpolation, control vidéo, lip-sync), orchestration (pipelines multi-modaux, API cloud) et applications (cas d'usage pédagogiques, fil rouge podcast audio→video). Clôture la couverture des 3 familles GenAI média (Audio / Image / Video) dans l'infrastructure i18n.

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/GenAI/Video/ \
    --src-lang fr \
    -o translations/genai-video/genai-video.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/genai-video/
```

Sortie attendue = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Voir aussi

- Issue #4957 — design infrastructure
- Epic #1650 — traduction multilingue du dépôt
- `scripts/translation/README.md` — schéma détaillé
