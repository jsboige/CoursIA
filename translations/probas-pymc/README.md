# translations/probas-pymc — synchro traduction i18n (#4957 Phase 2)

## Couverture

| Métrique | Valeur |
|----------|--------|
| Série source | `MyIA.AI.Notebooks/Probas/PyMC/` (programmation probabiliste bayésienne — PyMC, **Python**) |
| Notebooks source | **19** (PyMC-1 installation → PyMC-19, suite pédagogique progressive) |
| Cellules extraites | **567** (markdown + code tous kernels confondus, nbformat canonique, id stable) |
| Taille CSV | ~0,6 MB (567 enregistrements × 21 colonnes) |
| Langue pivot | **fr** (PIVOT_LANG = "fr", cf #1650 Phase 0.5) |
| Langues cibles | **en, es, ar, fa, zh, ru, pt** (7 langues vivantes côté Argumentum) |
| Date seed | 2026-07-11 |
| Source seed | PR THIS (Phase 2 rollout Probas/PyMC, nouvelle série Python) |

## Workflow T0→T3

T0 (catalogue CSV) **LIVRÉ** : le CSV seed `probas_pymc.csv` capture la substance canonique de la série au commit `04f8edf91`. Chaque enregistrement = `notebook, cell_id, cell_type, src_lang, src_hash, text_fr, text_<7 langues>, hash_fr, hash_<7 hash>`. Les hashes `sha256-16` sur le texte normalisé (rstrip lines + strip newlines) détectent les dérives cellule-par-cellule.

T1 (extraction) **LIVRÉ** : `python scripts/translation/extract_cells_to_csv.py MyIA.AI.Notebooks/Probas/PyMC/ -o translations/probas-pymc/probas_pymc.csv --src-lang fr --repo-root .`. Script déterministe (re-run vérifié). Exclut `_output.ipynb` (Papermill) et `_agent.ipynb` (auto-générés) via `endswith`. 567 cellules extraites des 19 notebooks. L'extracteur est agnostique au kernel (traite `markdown` + `code`) — pour les cellules code, seuls les commentaires sont à traduire (convention #4957 §1).

T2 (drift detector) **LIVRÉ** : `python scripts/translation/check_translation_sync.py translations/probas-pymc/probas_pymc.csv` → `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC round-trip). Workflow CI `.github/workflows/translation-drift.yml` non-bloquant read-only déclenche ce check sur PR paths `translations/**` + `MyIA.AI.Notebooks/**/*.ipynb` + `scripts/translation/**`.

T3 (moteur Argumentum) **GATED** : run du moteur #1650 Phase 1 (connecteur Argumentum → fill des colonnes `text_<lang>` pour chaque cellule). Reste gated sur l'activation du connecteur Argumentum.

## Régénération manuelle

Si la série `MyIA.AI.Notebooks/Probas/PyMC/` change (ajout/suppression de cellules, enrichissement, nouveaux notebooks), re-run déterministe :

```bash
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/Probas/PyMC/ \
    -o translations/probas-pymc/probas_pymc.csv --src-lang fr --repo-root .
```

T2 check post-régénération :

```bash
python scripts/translation/check_translation_sync.py \
    translations/probas-pymc/probas_pymc.csv
```

Anomalies attendues (T3 non livré) :
- `TRAD_DRIFT` attendu sur les `text_<lang>` et `hash_<lang>` tant que T3 n'a pas rempli les colonnes. Le seed CSV doit **demeurer avec `text_fr` rempli** (pivot) et **toutes les autres langues vides** (T3 à fill).
- `SRC_DRIFT` = changement upstream non reporté dans le CSV → relancement T1 obligatoire.

## Liaison upstream

- EPIC parent **#4957** (CSV-by-series + CI drift-flag + resync manuelle Argumentum)
- Phase 0.5 **#1650** (Argumentum connecteur + moteur de traduction)
- Substance lane **po-2025** (Python/PyMC = partition native) — série Probas/PyMC (Epic parité ML.Net→Python #4956)
- Voisin seed **translations/probas-infer/** (série Probas .NET, PR parallèle) + **translations/gametheory/** (13ᵉ série)

## Conformité règles

- **L327 `+N/-0` purement additif** : nouveau répertoire `probas-pymc/`, nouveau CSV (pas d'écrasement) + README.
- **catalog-pr-hygiene R1** : catalogue intact (CSV vit hors catalogue, sous `translations/`).
- **L335 anti-monoculture** : substance neuve Phase 2 (Probas/PyMC **Python** natif), variée vs ledgers/ICT des cycles précédents.
- **readme-french-first** : README rédigé en français (FR pivot Phase 0.5).
- **Stop & Repair** : pas de hand-edit de cellule — le CSV est un artefact dérivé déterministe (T1 determinism vérifié, secret scan 0 match).
