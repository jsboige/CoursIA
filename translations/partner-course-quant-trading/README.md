# CSV de synchro traduction — série QuantConnect/partner-course-quant-trading

**Statut** : Phase 2 rollout (Epic #4957 / #1650). Cours partenaire QuantConnect sponsorisé par Jared Broad (CEO QuantConnect, tier « Trading Firm »). Le sponsor a accès à QC-Py-01..04, aux exemples (Crypto-MultiCanal, Sector-Momentum, Trend-Following), au kit-transitoire ML (RandomForest/XGBoost/Framework-Composite) et aux templates étudiant (starter/intermediate/advanced/student-presentation).

## Couvert

| Fichier | Série | Notebooks seedés | Cellules |
|---------|-------|-------------------|----------|
| [`partner-course.csv`](partner-course.csv) | `MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/` | **2 / 7** notebooks research avec cell_id v4.5 | 25 cellules (markdown + code, 20 colonnes #4957 §1) |

Les 2 notebooks seedés sont :

- `examples/Sector-Momentum/deep_research_optimization.ipynb` (13 cells : 7 md + 6 code) — Sharpe optimization analysis (Sector-Momentum strategy, walk-forward, leverage grid, régime detection)
- `examples/Sector-Momentum/research_robustness.ipynb` (12 cells : 6 md + 6 code) — Robustness checks 2015-2025 sur régimes bull/COVID/bear/recovery/AI-Bull

**Schéma** : 20 colonnes ratifiées (#4957 §1). `src_lang=fr`, `src_hash` (sha256-16 sur texte normalisé) + `text_fr` remplies ; colonnes cibles (`text_en/es/ar/fa/zh/ru/pt`) vides en attendant le moteur T3 Argumentum (#1650 Phase 1 connecteur gated #1271).

**Note C.2/C.3 / scope kernels** : les 2 notebooks seedés sont en kernel `python3` standard (research notebooks Jupyter classiques). Pas de QuantBook (`QuantBook()`), pas de QC Cloud requis, pas de re-exécution possible localement (= dette #3968/#4362 connue ; reproducible only via QC Cloud ou data cache locale). L'extraction T1 ne touche pas au contenu exécutable, seulement aux cellules textuelles (markdown + commentaires dans cellules code).

## Dette extraction — migration nbformat v4.5 requise (follow-up)

Les **5 autres notebooks research** de la série ne sont **pas couverts** par cette extraction parce qu'ils sont en `nbformat < 4.5` (v4.2 ou v4.4) et n'exposent pas de `cell.id` stable — exigence canonique du script `extract_cells_to_csv.py` (lignes 78-91) pour détecter le drift cellule-par-cellule en T2 :

| Notebook | Version | Cells | Manque |
|----------|---------|-------|--------|
| `examples/Crypto-MultiCanal/research.ipynb` | v4.2 | 51 | 51 cell_id |
| `examples/Crypto-MultiCanal/research_archive.ipynb` | v4.2 | 68 | 68 cell_id |
| `kit-transitoire/01-ML-RandomForest/research.ipynb` | v4.4 | 18 | 18 cell_id |
| `kit-transitoire/02-ML-XGBoost/research.ipynb` | v4.4 | 18 | 18 cell_id |
| `kit-transitoire/03-Framework-Composite/research.ipynb` | v4.4 | 18 | 18 cell_id |

**Total dette migration** : **173 cells** sur 5 notebooks (subset de la dette globale QC = **89 notebooks** en `< v4.5` sur 204 inventoriés cf. investigation c.524, dont la vague canonique #6257/#6303/#6392/#6498 a déjà traité ~50+). La méthode canonique est documentée dans le body de la PR #6498 (c.457 : « add deterministic nbformat v4.5 cell ids, pattern `id = "cell-" + md5(... )[:8]`, ratio exact 2N/N add/del, no re-exec, validation `nbformat.validate()` strict PASS + `validate_pr_notebooks.py` 0 H.3/C.2 »).

**Recommandation follow-up** : ouvrir une PR dédiée `enrich(nbformat,#6257): add v4.5 cell ids to partner-course-quant-trading research (5 notebooks, ~172 cells)` dans la suite de la vague canonique #6257, puis régénérer ce CSV via `extract_cells_to_csv.py --update translations/partner-course-quant-trading/partner-course.csv` pour absorber les 173 cells manquantes (canon C458-L2 ★ : `--update` mono-cellule préserve les colonnes cibles T3). Sujet **hors scope** du présent PR (G.4 atomic = 1 sujet par PR).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading \
    -o translations/partner-course-quant-trading/partner-course.csv \
    --src-lang fr
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter après la migration v4.5 produira un CSV mis à jour (les 25 lignes actuelles + 173 nouvelles = **198 cellules totales** sur les 7 notebooks).

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
- `translations/quantconnect/README.md` — note #6782 ai-01 « resync short d'1 ligne — le prochain toucher ajoute la ligne ml-datascience (~708 cells, 28e CSV) »
