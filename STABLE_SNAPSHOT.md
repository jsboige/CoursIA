# STABLE_SNAPSHOT.md — Notebook Execution Forensic Audit

**Date**: 2026-07-17
**SHA**: `d8ea11a` (HEAD main)
**Tool**: `python scripts/notebook_tools/forensic_scan.py --with-git --json-out`
**Total notebooks scanned**: 934

---

## Executive Summary

| Category | Count | % | Status |
|----------|-------|---|--------|
| **A_ALL_EXEC_OK** | 869 | 93.0% | Healthy |
| **B_PARTIAL_EXEC** | 28 | 3.0% | Needs attention |
| **C_NEVER_EXECUTED** | 10 | 1.1% | Critical |
| **D_HAS_ERRORS** | 2 | 0.2% | Critical |
| **REFERENCE** | 25 | 2.7% | Expected |

**Actionable issues**: 40 notebooks (4.3%) across B/C/D categories.

---

## Per-Series Breakdown

| Series | Total | A (OK) | B (Partial) | C (Never) | D (Errors) | Ref | Health |
|--------|-------|--------|-------------|-----------|------------|-----|--------|
| **CaseStudies** | 6 | 6 | 0 | 0 | 0 | 0 | 100.0% |
| **GameTheory** | 55 | 55 | 0 | 0 | 0 | 0 | 100.0% |
| **GenAI** | 144 | 144 | 0 | 0 | 0 | 0 | 100.0% |

> **Note (issue #8050)** : GenAI = 144 inclut 3 notebooks `examples/` (`history-geography`, `literature-visual`, `science-diagrams`) présents dans le forensic scan mais **exclus du catalogue curé par design** (`EXCLUDE_PEDAGOGICAL = {..., "examples", ...}`, cf `scripts/notebook_tools/generate_catalog.py` ligne 39). Catalogue GenAI curé = 141 ; écart 144−141 = 3 = exclusions catalogue par design, **pas du drift**. Détail : `docs/reference/notebook-counts-reconciliation.md`.
| **IIT** | 31 | 31 | 0 | 0 | 0 | 0 | 100.0% |
| **ML** | 46 | 46 | 0 | 0 | 0 | 0 | 100.0% |
| **Probas** | 58 | 58 | 0 | 0 | 0 | 0 | 100.0% |
| **QuantConnect** | 204 | 142 | 27 | 9 | 1 | 25 | 69.6% |
| **RL** | 17 | 17 | 0 | 0 | 0 | 0 | 100.0% |
| **Search** | 114 | 114 | 0 | 0 | 0 | 0 | 100.0% |
| **Sudoku** | 36 | 36 | 0 | 0 | 0 | 0 | 100.0% |
| **SymbolicAI** | 222 | 220 | 1 | 0 | 1 | 0 | 99.1% |
| **TOP** | 1 | 0 | 0 | 1 | 0 | 0 | 0.0% |

---

## C_NEVER_EXECUTED (10 notebooks) — At least one cell with `execution_count: null`

| Notebook | Series | Last commit |
|----------|--------|-------------|
| `MyIA.AI.Notebooks/GradeBook.ipynb` | TOP | 2026-03-23 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-01-RiskParity-Composite.ipynb` | QuantConnect | 2026-07-12 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-02-SectorRotation-Momentum.ipynb` | QuantConnect | 2026-07-12 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-04-MeanReversion.ipynb` | QuantConnect | 2026-07-12 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-05-RegimeSwitching.ipynb` | QuantConnect | 2026-07-12 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-06-PCA-StatArb.ipynb` | QuantConnect | 2026-07-12 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-06-VolTargeting.ipynb` | QuantConnect | 2026-07-12 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-07-TemporalCNN.ipynb` | QuantConnect | 2026-07-12 |
| `MyIA.AI.Notebooks/QuantConnect/projects/Research-Executor/runner.ipynb` | QuantConnect | 2026-06-01 |
| `MyIA.AI.Notebooks/QuantConnect/research/research_m12_har_rv_j_minute.ipynb` | QuantConnect | 2026-06-28 |

---

## D_HAS_ERRORS (2 notebooks) — At least one error output

| Notebook | Series | n_err/n_code | Last commit |
|----------|--------|--------------|-------------|
| `MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/examples/Crypto-MultiCanal/research_archive.ipynb` | QuantConnect | 13/33 | 2026-07-16 |
| `MyIA.AI.Notebooks/SymbolicAI/archive/Tweety.ipynb` | SymbolicAI | 1/34 | 2026-06-22 |

---

## B_PARTIAL_EXEC (28 notebooks) — Some cells executed but not all

| Notebook | Series | n_exec/n_code | Last commit |
|----------|--------|---------------|-------------|
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-18-ML-Features-Engineering.ipynb` | QuantConnect | 22/25 | 2026-07-03 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-19-ML-Supervised-Classification.ipynb` | QuantConnect | 24/27 | 2026-07-12 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-30-LSTM-Training.ipynb` | QuantConnect | 16/19 | 2026-07-12 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-31-Transformer-Training.ipynb` | QuantConnect | 14/17 | 2026-07-12 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-35-RL-Portfolio-Construction.ipynb` | QuantConnect | 5/9 | 2026-07-12 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-40-PaperTrading-Binance.ipynb` | QuantConnect | 10/12 | 2026-07-14 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-41-PaperTrading-IBKR.ipynb` | QuantConnect | 9/12 | 2026-07-14 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-01-FinBERT-Sentiment.ipynb` | QuantConnect | 6/9 | 2026-07-02 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-02-ML-Classification.ipynb` | QuantConnect | 3/6 | 2026-07-02 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-04-RL-DQN-Trading.ipynb` | QuantConnect | 2/5 | 2026-06-27 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-05-MLP-Forecasting.ipynb` | QuantConnect | 2/5 | 2026-07-02 |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Dataset-Workflow.ipynb` | QuantConnect | 11/14 | 2026-07-15 |
| `MyIA.AI.Notebooks/QuantConnect/projects/BTC-ML/quantbook.ipynb` | QuantConnect | 3/11 | 2026-07-02 |
| `MyIA.AI.Notebooks/QuantConnect/projects/CSharp-BTC-MACD-ADX/Research.ipynb` | QuantConnect | 18/21 | 2026-04-21 |
| `MyIA.AI.Notebooks/QuantConnect/projects/Crypto-MultiCanal/quantbook.ipynb` | QuantConnect | 2/10 | 2026-07-02 |
| `MyIA.AI.Notebooks/QuantConnect/projects/DL-LSTM/quantbook.ipynb` | QuantConnect | 10/12 | 2026-06-02 |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-DeepLearning/quantbook.ipynb` | QuantConnect | 10/12 | 2026-06-02 |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-HeadShoulders-CNN/research.ipynb` | QuantConnect | 5/6 | 2026-06-02 |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-TextClassification/quantbook.ipynb` | QuantConnect | 4/14 | 2026-05-12 |
| `MyIA.AI.Notebooks/QuantConnect/projects/ML-XGBoost/quantbook.ipynb` | QuantConnect | 1/11 | 2026-06-02 |
| `MyIA.AI.Notebooks/QuantConnect/projects/Multi-Layer-EMA/research.ipynb` | QuantConnect | 2/6 | 2026-06-02 |
| `MyIA.AI.Notebooks/QuantConnect/projects/PairsTrading/quantbook.ipynb` | QuantConnect | 3/7 | 2026-05-12 |
| `MyIA.AI.Notebooks/QuantConnect/projects/RL-Portfolio/quantbook.ipynb` | QuantConnect | 3/10 | 2026-07-02 |
| `MyIA.AI.Notebooks/QuantConnect/projects/Research-Executor/research_defensive_etf_rotation.ipynb` | QuantConnect | 1/5 | 2026-06-02 |
| `MyIA.AI.Notebooks/QuantConnect/projects/Research-Executor/research_long_short_harvest.ipynb` | QuantConnect | 2/4 | 2026-06-01 |
| `MyIA.AI.Notebooks/QuantConnect/projects/Research-Executor/research_macro_factor_rotation.ipynb` | QuantConnect | 2/4 | 2026-06-01 |
| `MyIA.AI.Notebooks/QuantConnect/projects/VIX-TermStructure/quantbook.ipynb` | QuantConnect | 2/10 | 2026-06-02 |
| `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/groupe-I2-contre-arguments-aspic/I2_Contre_arguments_ASPIC.ipynb` | SymbolicAI | 23/25 | 2026-07-16 |

---

## References

- `scripts/notebook_tools/forensic_scan.py` — scan source
- [CLAUDE.md §H.7](CLAUDE.md) — Plan P0-P4 cycle perpétuel (P4 = monthly regen)
- Previous snapshot: see `docs/archive/STABLE_SNAPSHOT.md`

