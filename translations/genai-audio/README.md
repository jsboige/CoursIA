# CSV de synchro traduction — série GenAI/Audio

**Statut** : Phase 0.5 backfill (Epic #4957 / #1650). Série GenAI/Audio couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`genai-audio.csv`](genai-audio.csv) | `GenAI/Audio/` (4 sous-niveaux : 01-Foundation, 02-Advanced, 03-Orchestration, 04-Applications) | 30 | 1128 (21 colonnes) |

**Note owner-lane** : l'extraction i18n est **safe owner-lane** (artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks).

**Périmètre fonctionnel** : la série couvre le pipeline audio IA — synthèse vocale (TTS, OpenAI/Kokoro), reconnaissance vocale (STT, Whisper API/local), opérations de base sur le signal (librosa, spectrogrammes, MFCC), orchestration et applications (podcast fil rouge). Le fil rouge podcast traverse les 4 sous-niveaux.

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/GenAI/Audio/ \
    --src-lang fr \
    -o translations/genai-audio/genai-audio.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/genai-audio/
```

Sortie attendue = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Voir aussi

- Issue #4957 — design infrastructure
- Epic #1650 — traduction multilingue du dépôt
- `scripts/translation/README.md` — schéma détaillé
