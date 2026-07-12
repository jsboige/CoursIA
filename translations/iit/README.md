# translations/iit — synchro traduction i18n (#4957 Phase 2)

## Couverture

| Métrique | Valeur |
|----------|--------|
| Série source | `MyIA.AI.Notebooks/IIT/` (PyPhi + ICT-Series : information intégrée, émergence, workspace — Python) |
| Notebooks source | **29** (3 IIT PyPhi + 26 ICT-Series) |
| Cellules extraites | **731** (428 markdown + 303 code, nbformat canonique, 99 % avec id stable) |
| Taille CSV | ~743 KB (731 enregistrements × 21 colonnes) |
| Langue pivot | **fr** (PIVOT_LANG = "fr", cf #1650 Phase 0.5 / #4980 Lean i18n) |
| Langues cibles | **en, es, ar, fa, zh, ru, pt** (7 langues vivantes côté Argumentum) |
| Date seed | 2026-07-10 |
| Source seed | PR THIS (Phase 2 rollout IIT, 11e série) |

## Workflow T0→T3

T0 (catalogue CSV) **LIVRÉ** : le CSV seed `iit.csv` capture la substance canonique de la série au commit `a93a08e21`. Chaque enregistrement = `notebook, cell_id, cell_type, src_lang, src_hash, text_fr, text_<7 langues>, hash_fr, hash_<7 hash>`. Les hashes `sha256-16` sur le texte normalisé (rstrip lines + strip newlines) détectent les dérives cellule-par-cellule.

T1 (extraction) **LIVRÉ** : `python scripts/translation/extract_cells_to_csv.py MyIA.AI.Notebooks/IIT/ -o translations/iit/iit.csv --src-lang fr --repo-root .`. Script déterministe byte-identique (cf `extract_cells_to_csv.py`). Exclut `_output.ipynb` (Papermill) et `_agent.ipynb` (auto-générés) via `endswith`. 731/738 cellules markdown/code extraites (7 sans id nbformat stable sautées — non traduisibles de façon fiable).

T2 (drift detector) **LIVRÉ** : `python scripts/translation/check_translation_sync.py translations/iit/iit.csv` → `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC round-trip). Workflow CI `.github/workflows/translation-drift.yml` non-bloquant read-only déclenche ce check sur PR paths `translations/**` + `MyIA.AI.Notebooks/**/*.ipynb` + `scripts/translation/**`.

T3 (moteur Argumentum) **GATED** : run du moteur #1650 Phase 1 (connecteur Argumentum → fill des colonnes `text_<lang>` pour chaque cellule). Reste gated sur l'activation du connecteur Argumentum.

## Régénération manuelle

Si la série `MyIA.AI.Notebooks/IIT/` change (ajout/suppression de cellules, enrichissement), re-run déterministe :

```bash
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/IIT/ \
    -o translations/iit/iit.csv --src-lang fr --repo-root .
```

T2 check post-régénération :

```bash
python scripts/translation/check_translation_sync.py \
    translations/iit/iit.csv
```

Anomalies attendues (T3 non livré) :
- `TRAD_DRIFT` attendu sur les `text_<lang>` et `hash_<lang>` tant que T3 n'a pas rempli les colonnes. Le seed CSV doit **demeurer avec `text_fr` rempli** (pivot) et **toutes les autres langues vides** (T3 à fill).
- `SRC_DRIFT` = changement upstream non reporté dans le CSV → relancement T1 obligatoire.

## Liaison upstream

- EPIC parent **#4957** (CSV-by-series + CI drift-flag + resync manuelle Argumentum)
- Phase 0.5 **#1650** (Argumentum connecteur + moteur de traduction)
- Substance owner-lane **#4588** (ICT-Series Epic, strate 5) + **#5681** (J-Lens Track S, tête-à-tête SAE⇄J-space)
- Voisin seed **translations/probas-infer/** (série précédente Phase 2)

## Conformité règles

- **L327 `+N/-0` purement additif** : nouveau répertoire `iit/`, nouveau CSV (pas d'écrasement) + README.
- **catalog-pr-hygiene R1** : catalogue intact (CSV vit hors catalogue, sous `translations/`).
- **L335 anti-monoculture** : substance neuve Phase 2 (IIT/ICT-Series), pas re-sweep monotone.
- **L143 SAFE cross-owner** : IIT/ICT = owner po-2025 (strate 5, Epic #4588 + #5681).
- **L289 anti-doublon** : 1 série = 1 PR de seed, PR Phase 2 distincte.
- **readme-french-first** : README rédigé en français (FR pivot Phase 0.5).
- **Stop & Repair** : pas de hand-edit de cellule, pas de scrub de sortie — le CSV est un artefact dérivé déterministe (T1 determinism byte-identique vérifié).

## Note de maintenance (smell signalé, hors-scope)

`ICT-19` apparaît en **double** dans la série : `ICT-19-EnjeuBattery.ipynb` + `ICT-19-EnjeuBattery-Raffinement.ipynb`. Les deux sont extraits tels quels dans le seed (le CSV suit la réalité du dépôt). Numéro dupliqué à clarifier en sujet séparé (signalé au dashboard coordinateur).
