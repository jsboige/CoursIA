# CSV de synchro traduction — série GenAI/FineTuning

**Statut** : Phase 0.5 backfill (Epic #4957 / #1650). Série `GenAI/FineTuning/` couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`genai-finetuning.csv`](genai-finetuning.csv) | `GenAI/FineTuning/` (5 notebooks : Introduction, QLoRA, SFT, RLHF/DPO, Model Merging & Routing) | 5 | 161 (21 colonnes) |

Répartition : 71 cellules `code` + 90 cellules `markdown` (prose pédagogique FR). Pivot `src_lang = fr` pour les 161 cellules (Phase 0.5, cf [#readme-french-first](../../.claude/rules/readme-french-first.md)). Les colonnes cibles T3 (`text_en`/`hash_en`/…/`text_pt`/`hash_pt`) restent vides en attente du run moteur Argumentum (gated #1650 Phase 1).

**Note owner-lane** : l'extraction i18n est **safe owner-lane** (artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks). Cette série est distincte de `translations/genai-casestudies/` (cas d'usage agentiques) et couvre la chaîne d'entraînement/post-entraînement des LLM.

**Périmètre fonctionnel** : la série parcourt le fine-tuning de bout en bout — introduction aux stratégies (FT-01), quantification QLoRA 4-bit (FT-02), supervised fine-tuning sur dataset instruct (FT-03), alignement par préférences RLHF/DPO (FT-04), fusion de modèles et routing MoE (FT-05). Python (kernel `python3`), appels aux frameworks ML (transformers, peft, trl, bitsandbytes).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/GenAI/FineTuning/ \
    -o translations/genai-finetuning/genai-finetuning.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV (vérifié : SHA256 `9ca37363f0…` reproductible).

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/genai-finetuning/genai-finetuning.csv
# -> 0 anomalie (intégrité src_hash == hash_fr sur les 161 cellules)
```

## Voir aussi

- Issue #4957 — design infrastructure T1→T2→T3
- Epic #1650 — traduction multilingue du dépôt
- [`translations/README.md`](../README.md) — arborescence globale des CSV
- `scripts/translation/README.md` — schéma détaillé des colonnes
