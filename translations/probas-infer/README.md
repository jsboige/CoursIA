# translations/probas-infer — synchro traduction i18n (#4957 Phase 2)

## Couverture

| Métrique | Valeur |
|----------|--------|
| Série source | `MyIA.AI.Notebooks/Probas/Infer/` (Infer.NET probabilistic programming, .NET Interactive) |
| Notebooks source | **19** (post-renum narratif #5637 c.377 — cycle 5/7/9/11/14) |
| Cellules extraites | **902** (code + markdown, nbformat canonique) |
| Taille CSV | ~844 KB (16 073 lignes CSV = header + 902 × 18 colonnes hash + texte) |
| Langue pivot | **fr** (PIVOT_LANG = "fr", cf #1650 Phase 0.5 / #4980 Lean i18n) |
| Langues cibles | **en, es, ar, fa, zh, ru, pt** (7 langues vivantes côté Argumentum) |
| Date seed | 2026-07-09 |
| Source seed | PR #5385 (Argument_Analysis) + PR #5799 (resync T1) + PR THIS (Phase 2 rollout) |

## Workflow T0→T3

T0 (catalogue CSV) **LIVRÉ** : le CSV seed `probas_infer.csv` capture la substance canonique de la série au commit `2e57ff283...` + la branche Phase 2. Chaque ligne = `notebook, cell_id, cell_type, src_lang, src_hash, text_fr, text_<7 langues>, hash_fr, hash_<7 hash>`. Les hashes `sha256-16` sur le texte normalisé (rstrip lines + strip newlines) détectent les dérives cellule-par-cellule.

T1 (extraction) **LIVRÉ** : `python3 scripts/translation/extract_cells_to_csv.py MyIA.AI.Notebooks/Probas/Infer/ -o translations/probas-infer/probas_infer.csv`. Script déterministe byte-identique (cf `extract_cells_to_csv.py` livré Phase 1 #5657 c.293-294). Exclut `_output.ipynb` (Papermill) et `_agent.ipynb` (auto-générés) via `endswith`.

T2 (drift detector) **LIVRÉ** : `python3 scripts/translation/check_translation_sync.py translations/probas-infer/probas_infer.csv` → `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC round-trip). Workflow CI `.github/workflows/translation-drift.yml` non-bloquant read-only déclenche ce check sur PR paths `translations/**` + `MyIA.AI.Notebooks/**/*.ipynb` + `scripts/translation/**`.

T3 (moteur Argumentum) **GATED** : run du moteur #1650 Phase 1 (connecteur OpenTelemetry/Argumentum → fill des colonnes `text_<lang>` pour chaque cellule). Reste gated sur l'activation du connecteur Argumentum (substance owner-lane po-2025 c.371-372).

## Régénération manuelle

Si la série `MyIA.AI.Notebooks/Probas/Infer/` change (renum, ajout/suppression de cellules), re-run déterministe :

```bash
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/Probas/Infer/ \
    -o translations/probas-infer/probas_infer.csv
```

T2 check post-régénération :

```bash
python scripts/translation/check_translation_sync.py \
    translations/probas-infer/probas_infer.csv
```

Anomalies attendues (T3 non livré) :
- `TRAD_DRIFT` attendu sur les `text_<lang>` et `hash_<lang>` tant que T3 n'a pas rempli les colonnes. Le seed CSV doit **demeurer avec `text_fr` rempli** (pivot) et **toutes les autres langues vides** (T3 à fill).
- `SRC_DRIFT` = changement upstream non reporté dans le CSV → relancement T1 obligatoire.

## Liaison upstream

- EPIC parent **#4957** (CSV-by-series + CI drift-flag + resync manuelle Argumentum)
- Phase 0.5 **#1650** (Argumentum connecteur + moteur de traduction)
- Substance owner-lane **#5637** (renum narratif, source des 19 notebooks)
- Voisin seed **translations/symbolicai/** (Argument_Analysis, PR THIS série 1 Phase 2)

## Conformité règles

- **L327 `+N/-0` purement additif** : nouveau répertoire `probas-infer/`, nouveau CSV (pas d'écrasement) + README.
- **catalog-pr-hygiene R1** : catalogue intact (CSV vit hors catalogue, sous `translations/`).
- **L335 anti-monoculture** : substance neuve Phase 2 (Probas/Infer), pas re-sweep monotone.
- **L143 SAFE cross-owner** : Probas/Infer = owner po-2025 (renum c.377 owner-lane + multiple cycles Probas).
- **L289 anti-doublon** : 1 série = 1 PR de seed, PR Phase 2 distincte des PRs Argument_Analysis (#5385 + #5799).
- **Stop & Repair** : pas de hand-edit de cellule, pas de scrub de sortie — le CSV est un artefact dérivé déterministe.
