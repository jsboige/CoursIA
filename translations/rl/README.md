# translations/rl — synchro traduction i18n (#4957 Phase 2)

## Couverture

| Métrique | Valeur |
|----------|--------|
| Série source | `MyIA.AI.Notebooks/RL/` (reinforcement learning — DQN, PPO, SAC, GRPO, multi-agent, Python) |
| Notebooks source | **17** (rl_1 intro cartpole → rl_13 curiosity/exploration, + sous-séries rl_6b/6c/6d/6e) |
| Cellules extraites | **486** (275 markdown + 211 code, nbformat canonique, 95 % avec id stable) |
| Taille CSV | ~450 KB (486 enregistrements × 21 colonnes) |
| Langue pivot | **fr** (PIVOT_LANG = "fr", cf #1650 Phase 0.5 / #4980 Lean i18n) |
| Langues cibles | **en, es, ar, fa, zh, ru, pt** (7 langues vivantes côté Argumentum) |
| Date seed | 2026-07-10 |
| Source seed | PR THIS (Phase 2 rollout RL, 12e série) |

## Workflow T0→T3

T0 (catalogue CSV) **LIVRÉ** : le CSV seed `rl.csv` capture la substance canonique de la série au commit `a93a08e21`. Chaque enregistrement = `notebook, cell_id, cell_type, src_lang, src_hash, text_fr, text_<7 langues>, hash_fr, hash_<7 hash>`. Les hashes `sha256-16` sur le texte normalisé (rstrip lines + strip newlines) détectent les dérives cellule-par-cellule.

T1 (extraction) **LIVRÉ** : `python scripts/translation/extract_cells_to_csv.py MyIA.AI.Notebooks/RL/ -o translations/rl/rl.csv --src-lang fr --repo-root .`. Script déterministe byte-identique. Exclut `_output.ipynb` (Papermill) et `_agent.ipynb` (auto-générés). 486/511 cellules markdown/code extraites (25 sans id nbformat stable sautées).

T2 (drift detector) **LIVRÉ** : `python scripts/translation/check_translation_sync.py translations/rl/rl.csv` → `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC round-trip). Workflow CI `.github/workflows/translation-drift.yml` non-bloquant read-only.

T3 (moteur Argumentum) **GATED** : run du moteur #1650 Phase 1 (connecteur Argumentum → fill des colonnes `text_<lang>`). Reste gated sur l'activation du connecteur.

## Régénération manuelle

```bash
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/RL/ \
    -o translations/rl/rl.csv --src-lang fr --repo-root .
python scripts/translation/check_translation_sync.py translations/rl/rl.csv
```

Anomalies attendues (T3 non livré) : `TRAD_DRIFT` sur les `text_<lang>`/`hash_<lang>` vides (normal tant que T3 n'a pas rempli). `SRC_DRIFT` = changement upstream → relancement T1.

## Liaison upstream

- EPIC parent **#4957** (CSV-by-series + CI drift-flag + resync manuelle Argumentum)
- Phase 0.5 **#1650** (Argumentum connecteur + moteur de traduction)
- Substance lane **#3360** (RL reward-shaping bug, po-2025) + série RL
- Voisin seed **translations/iit/** (série précédente Phase 2, PR parallèle)

## Conformité règles

- **L327 `+N/-0` purement additif** : nouveau répertoire `rl/`, nouveau CSV + README.
- **catalog-pr-hygiene R1** : catalogue intact (CSV vit hors catalogue, sous `translations/`).
- **L335 anti-monoculture** : substance neuve Phase 2 (RL), variée vs IIT livré parallèle.
- **readme-french-first** : README rédigé en français (FR pivot Phase 0.5).
- **Stop & Repair** : pas de hand-edit de cellule — le CSV est un artefact dérivé déterministe (T1 determinism byte-identique vérifié).
