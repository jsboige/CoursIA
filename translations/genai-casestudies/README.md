# CSV de synchro traduction — série GenAI/CaseStudies

**Statut** : Phase 0.5 backfill (Epic #4957 / #1650). Série `GenAI/CaseStudies/` couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`genai-casestudies.csv`](genai-casestudies.csv) | `GenAI/CaseStudies/` (4 études de cas GenAI agentiques : Barbie-Schreck, Fort-Boyard, Medical-Chatbot, Recipe-Maker) | 4 | 113 (21 colonnes) |

Répartition : 54 cellules `code` + 59 cellules `markdown` (prose pédagogique FR). Pivot `src_lang = fr` pour les 113 cellules (Phase 0.5, cf [#readme-french-first](../../.claude/rules/readme-french-first.md)). Les colonnes cibles T3 (`text_en`/`hash_en`/…/`text_pt`/`hash_pt`) restent vides en attente du run moteur Argumentum (gated #1650 Phase 1).

**Note owner-lane** : l'extraction i18n est **safe owner-lane** (artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks). Cette série est distincte de `translations/casestudies/` qui couvre les études de cas top-level (`CaseStudies/Diagnostic-Medical`, `Oncology-Planning`, `SmartGrid-Energy`).

**Périmètre fonctionnel** : la série illustre l'agent GenAI de bout en bout sur 4 cas concrets — génération d'images thématiques (Barbie-Schreck), orchestration multi-outils ludique (Fort-Board), assistant médical RAG (Medical-Chatbot), et assistant culinaire multimodal (Recipe-Maker). Python (kernel `python3`), appels aux services GenAI locaux (ComfyUI/Qwen via la stack Docker).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/GenAI/CaseStudies/ \
    -o translations/genai-casestudies/genai-casestudies.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV (vérifié : SHA256 `bcf08c94…` reproductible).

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/genai-casestudies/genai-casestudies.csv
```

Résultat attendu : `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC by construction pour un seed frais). Les drifts (`SRC_DRIFT` / `TRAD_DRIFT`) apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).
