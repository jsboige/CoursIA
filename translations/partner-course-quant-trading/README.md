# CSV de synchro traduction — série QuantConnect/partner-course-quant-trading

**Statut** : Phase 2 rollout (Epic #4957 / #1650). Cours partenaire QuantConnect sponsorisé par Jared Broad (CEO QuantConnect, tier « Trading Firm »). Le sponsor a accès à QC-Py-01..04, aux exemples (Crypto-MultiCanal, Sector-Momentum, Trend-Following), au kit-transitoire ML (RandomForest/XGBoost/Framework-Composite) et aux templates étudiant (starter/intermediate/advanced/student-presentation).

## Couvert

| Fichier | Série | Notebooks seedés | Cellules |
|---------|-------|-------------------|----------|
| [`partner-course.csv`](partner-course.csv) | `MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/` | **2 / 7** au seed 2026-07-16 (notebooks research avec cell_id v4.5 — le périmètre courant vit dans le CSV) | 25 au seed 2026-07-16 (cellules markdown + code, 21 colonnes #4957 §1 — compte courant mesurable dans le CSV) |

Les deux notebooks seedés au seed 2026-07-16 étaient :

- `examples/Sector-Momentum/deep_research_optimization.ipynb` (cells 13 : 7 md + 6 code) — Sharpe optimization analysis (Sector-Momentum strategy, walk-forward, leverage grid, régime detection)
- `examples/Sector-Momentum/research_robustness.ipynb` (cells 12 : 6 md + 6 code) — Robustness checks 2015-2025 sur régimes bull/COVID/bear/recovery/AI-Bull

**Schéma** : 21 colonnes ratifiées (#4957 §1). `src_lang=fr`, `src_hash` (sha256-16 sur texte normalisé) + `text_fr` remplies ; colonnes cibles (`text_en/es/ar/fa/zh/ru/pt`) vides en attendant le moteur T3 Argumentum (#1650 Phase 1 connecteur gated #1271).

**Note C.2/C.3 / scope kernels** : les notebooks seedés sont en kernel `python3` standard (research notebooks Jupyter classiques). Pas de QuantBook (`QuantBook()`), pas de QC Cloud requis, pas de re-exécution possible localement (= dette #3968/#4362 connue ; reproducible only via QC Cloud ou data cache locale). L'extraction T1 ne touche pas au contenu exécutable, seulement aux cellules textuelles (markdown + commentaires dans cellules code).

## Dette extraction — migration nbformat v4.5 requise (follow-up, snapshot au seed 2026-07-16)

Les cinq autres notebooks research de la série n'étaient **pas couverts** par cette extraction à l'époque, parce qu'ils étaient en `nbformat < 4.5` (v4.2 ou v4.4) et n'exposaient pas de `cell.id` stable — exigence canonique du script `extract_cells_to_csv.py` (lignes 78-91) pour détecter le drift cellule-par-cellule en T2 :

| Notebook | Version | Cells | Manque |
|----------|---------|-------|--------|
| `examples/Crypto-MultiCanal/research.ipynb` | v4.2 | 51 | 51 cell_id |
| `examples/Crypto-MultiCanal/research_archive.ipynb` | v4.2 | 68 | 68 cell_id |
| `kit-transitoire/01-ML-RandomForest/research.ipynb` | v4.4 | 18 | 18 cell_id |
| `kit-transitoire/02-ML-XGBoost/research.ipynb` | v4.4 | 18 | 18 cell_id |
| `kit-transitoire/03-Framework-Composite/research.ipynb` | v4.4 | 18 | 18 cell_id |

**Total dette migration** : cells à l'époque du seed **173**, sur cinq notebooks (subset de la dette globale QC mesurée à l'époque de l'investigation c.524 : notebooks en `< v4.5` **89**, sur 204 inventoriés, dont la vague canonique #6257/#6303/#6392/#6498 avait déjà traité ~50+ — mesures historiques, non reprises depuis). La méthode canonique est documentée dans le body de la PR #6498 (c.457 : « add deterministic nbformat v4.5 cell ids, pattern `id = "cell-" + md5(... )[:8]`, ratio exact 2N/N add/del, no re-exec, validation `nbformat.validate()` strict PASS + `validate_pr_notebooks.py` 0 H.3/C.2 »).

**Recommandation follow-up (rédigée à l'époque du seed)** : ouvrir une PR dédiée `enrich(nbformat,#6257): add v4.5 cell ids to partner-course-quant-trading research` (titre alors proposé, pour la migration des cellules restantes d'alors) dans la suite de la vague canonique #6257, puis régénérer ce CSV via `extract_cells_to_csv.py --update translations/partner-course-quant-trading/partner-course.csv` pour absorber les manquantes d'alors (canon C458-L2 ★ : `--update` mono-cellule préserve les colonnes cibles T3). Sujet **hors scope** du présent PR (G.4 atomic = 1 sujet par PR).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading \
    -o translations/partner-course-quant-trading/partner-course.csv \
    --src-lang fr
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter après la migration v4.5 produirait un CSV mis à jour (à l'époque du seed : lignes en place 25 + nouvelles 173, soit un total attendu de 198 — sur les sept notebooks de la série, compte courant dans le CSV).

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py \
    translations/partner-course-quant-trading/partner-course.csv
```

Résultat à l'extraction : `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` — `OK : 1 CSV vérifié(s), 0 drift` (IN_SYNC par construction T1, attendu avant T3 Argumentum).

## Pre-flight secret

Les notebooks recherche sont en Python 3 (research) + QuantConnect (templates) + Cloud-First workflow sponsorisé. Risque secret modéré (peu d'API externe, mais zappa et levée récente sur le sponsoring QuantConnect = check de rigueur) :

- Recherche `sk-*` / `ghp_*` / `hf_*` / `AIza*` / `os.getenv(..., "literal")` sur le CSV seedé : **0 hit** (pré-commit L327 / secrets-hygiene rule 6 + scanner gitleaks `.pre-commit-config.yaml` v8.21.2).
- Pas de token sponsorisé QuantConnect dans le code (authentification gérée hors-templates).

## Hors scope

- `partner-course-quant-trading/templates/{starter,intermediate,advanced}/main.py` — **code Python sponsorisé** sponsor-tier partenaire, pas des notebooks. Le pattern « code sponsorisé » est exclu des CSV de synchro (artefact dérivé = markdown + ipynb, pas `.py` de template réutilisable par les étudiants).
- `partner-course-quant-trading/scripts/*.py` — scripts utilitaires QC backtest, hors périmètre traduction multilingue.
- `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-*.ipynb` — la série QC-Py principale est déjà couverte par `translations/quantconnect/quantconnect-py.csv` (PR #6765 MERGED).
- `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/research_*.ipynb` — série ML-Training distincte, future vague séparée après migration v4.5 des 14 research notebooks concernés.

## Voir aussi

- Issue #4957 — design infrastructure synchronisation traduction (Epic parent)
- Issue #6257 — vague canonique migration nbformat v4.5 (méthode + ratios add/del)
- PR #6498 — precedent « enrich(nbformat,#6257): add v4.5 cell ids to QuantConnect research cluster » (12 ids / 3 nb, c.457)
- PR #6765 — precedent « feat(translation,#4957): seed CSV for QuantConnect/Python QC-Py series (T1 Phase 0.5) » (sibling wave même dossier `translations/quantconnect/`)
- Epic #1650 — traduction multilingue du dépôt (Phase 0.5 = ce backfill ; Phase 1+ = moteur Argumentum scripté gated #1271)
- `translations/quantconnect/README.md` — note #6782 ai-01 : resync court ; le prochain toucher y ajoute la ligne ml-datascience.
