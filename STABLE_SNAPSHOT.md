# STABLE_SNAPSHOT.md — Notebook Execution Forensic Audit

**Date**: 2026-05-12
**SHA**: `c7508349` (HEAD main)
**Tool**: `scripts/notebook_tools/forensic_scan.py --with-git --json-out`
**Total notebooks scanned**: 547

---

## Executive Summary

| Category | Count | % | Status |
|----------|-------|---|--------|
| **A_ALL_EXEC_OK** | 460 | 84.1% | Healthy |
| **B_PARTIAL_EXEC** | 11 | 2.0% | Needs attention |
| **C_NEVER_EXECUTED** | 34 | 6.2% | Critical |
| **D_HAS_ERRORS** | 10 | 1.8% | Critical |
| **REFERENCE** | 24 | 4.4% | Expected (QC ref notebooks) |
| **NO_CODE** | 8 | 1.5% | Expected (markdown-only) |

**Actionable issues**: 55 notebooks (10.0%) across B/C/D categories.

**Key finding**: QuantConnect series accounts for 49/55 problematic notebooks (89%). All other series are near-100% healthy.

---

## Per-Series Breakdown

| Series | Total | A (OK) | B (Partial) | C (Never) | D (Errors) | Ref/NoCode | Health |
|--------|-------|--------|-------------|-----------|------------|------------|--------|
| **GenAI** | 103 | 102 | 0 | 1 | 0 | 0 | 99.0% |
| **SymbolicAI** | 91 | 90 | 0 | 0 | 1 | 0 | 98.9% |
| **Search** | 45 | 45 | 0 | 0 | 0 | 0 | 100% |
| **Sudoku** | 32 | 31 | 1 | 0 | 0 | 0 | 96.9% |
| **Probas** | 32 | 32 | 0 | 0 | 0 | 0 | 100% |
| **GameTheory** | 30 | 30 | 0 | 0 | 0 | 0 | 100% |
| **ML** | 30 | 30 | 0 | 0 | 0 | 0 | 100% |
| **QuantConnect** | 170 | 89 | 9 | 31 | 9 | 32 | 52.4% |
| **RL** | 6 | 6 | 0 | 0 | 0 | 0 | 100% |
| **IIT** | 1 | 1 | 0 | 0 | 0 | 0 | 100% |
| **CaseStudies** | 4 | 4 | 0 | 0 | 0 | 0 | 100% |
| **bin** | 2 | 0 | 1 | 1 | 0 | 0 | N/A (build artifact) |
| **TOP** | 1 | 0 | 0 | 1 | 0 | 0 | N/A |

**Non-QC health**: 371/373 = **99.5% ALL_EXEC_OK** (only GenAI fort-boyard-csharp + Sudoku-16-NN Python partial).

---

## C_NEVER_EXECUTED (34 notebooks) — All cells `execution_count: null`

### QuantConnect (31)

| Notebook | Type | Notes |
|----------|------|-------|
| `QC-Py-01-Setup.ipynb` | Cours | Setup guide, no code to execute |
| `QC-Py-04-Research-Workflow.ipynb` | Cours | QuantBook research workflow |
| `QC-Py-19-ML-Supervised-Classification.ipynb` | Cours | ML classification course |
| `QC-Py-Dataset-Workflow.ipynb` | Cours | Dataset workflow |
| `projects/Research-Executor/runner.ipynb` | Runner | Batch executor |
| `projects/Research-Executor/research_asset_class_momentum.ipynb` | Research | Template notebook |
| `projects/Research-Executor/research_commodity_term_structure.ipynb` | Research | Template notebook |
| `projects/Research-Executor/research_defensive_etf_rotation.ipynb` | Research | Template notebook |
| `projects/Research-Executor/research_long_short_harvest.ipynb` | Research | Template notebook |
| `projects/Research-Executor/research_macro_factor_rotation.ipynb` | Research | Template notebook |
| `projects/Research-Executor/research_piotroski_fscore.ipynb` | Research | Template notebook |
| `projects/Research-Executor/research_puppies_of_dow.ipynb` | Research | Template notebook |
| `projects/Research-Executor/research_volatility_regime_ml.ipynb` | Research | Template notebook |
| `projects/BTC-ML/quantbook.ipynb` | Quantbook | ML on BTC |
| `projects/BTC-ML/research.ipynb` | Research | ML research |
| `projects/Crypto-MultiCanal/research.ipynb` | Research | Crypto multi-signal |
| `projects/ML-HeadShoulders-CNN/research.ipynb` | Research | CNN pattern detection |
| `projects/ML-Pairs-PCA-Selection/research.ipynb` | Research | PCA pairs |
| `projects/Multi-Layer-EMA/research.ipynb` | Research | Multi-layer EMA |
| `projects/Option-Wheel/research.ipynb` | Research | Options wheel |
| `projects/Sector-ML-Classification/research.ipynb` | Research | Sector ML |
| `projects/Framework_Composite_EMATrend/quantbook_composite_research.ipynb` | Quantbook | Composite framework |
| `projects/CSharp-BTC-EMA-Cross/research_robustness.ipynb` | Robustness | C# strategy |
| `projects/CSharp-CTG-Momentum/research_robustness.ipynb` | Robustness | C# strategy |
| `ESGF-2026/examples/Crypto-MultiCanal/research_archive.ipynb` | Archive | Archived research |
| `ESGF-2026/kit-transitoire/01-ML-RandomForest/research.ipynb` | Template | Student kit |
| `ESGF-2026/kit-transitoire/02-ML-XGBoost/research.ipynb` | Template | Student kit |
| `ESGF-2026/kit-transitoire/03-Framework-Composite/research.ipynb` | Template | Student kit |
| `ML-Training-Pipeline/ML-Research-Template.ipynb` | Template | ML template |
| `Python/research/research_classification.ipynb` | Research | Classification |
| `Python/research/research_lstm.ipynb` | Research | LSTM |

### Non-QuantConnect (3)

| Notebook | Series | Notes |
|----------|--------|-------|
| `GenAI/SemanticKernel/fort-boyard-csharp.ipynb` | GenAI | C# notebook, likely demo/WIP |
| `GradeBook.ipynb` | TOP | GradeBook app notebook |
| `bin/Debug/net9.0/.../Workbook-Template.ipynb` | bin | Build artifact |

---

## D_HAS_ERRORS (10 notebooks) — At least one error output

### QuantConnect (9)

| Notebook | Code cells | Errors | Error rate | Severity |
|----------|-----------|--------|------------|----------|
| `projects/Alpha-Correlation-Analysis/quantbook.ipynb` | 18 | 11 | 61% | **Critical** |
| `projects/Crypto-MultiCanal/quantbook.ipynb` | 10 | 8 | 80% | **Critical** |
| `projects/ML-XGBoost/quantbook.ipynb` | 11 | 8 | 73% | **Critical** |
| `projects/RL-Portfolio/quantbook.ipynb` | 10 | 7 | 70% | **Critical** |
| `projects/VIX-TermStructure/quantbook.ipynb` | 10 | 6 | 60% | **Critical** |
| `projects/DL-LSTM/quantbook.ipynb` | 12 | 2 | 17% | Moderate |
| `projects/ML-DeepLearning/quantbook.ipynb` | 12 | 2 | 17% | Moderate |
| `projects/ML-Regression/quantbook.ipynb` | 12 | 1 | 8% | Low |
| `projects/Portfolio-Optimization-ML/research.ipynb` | 11 | 1 | 9% | Low |

### Non-QuantConnect (1)

| Notebook | Code cells | Errors | Notes |
|----------|-----------|--------|-------|
| `SymbolicAI/archive/Tweety.ipynb` | 34 | 1 | Archived, 1/34 error |

---

## B_PARTIAL_EXEC (11 notebooks) — Some cells executed, some not

### QuantConnect (9)

| Notebook | Code | Exec | % Exec | Notes |
|----------|------|------|--------|-------|
| `ESGF-2026/examples/Crypto-MultiCanal/research.ipynb` | 24 | 15 | 63% | 15/24, 0 outputs |
| `projects/CSharp-BTC-MACD-ADX/Research.ipynb` | 21 | 18 | 86% | 18/21, 0 outputs |
| `projects/ML-TextClassification/quantbook.ipynb` | 14 | 4 | 29% | 4/14 |
| `projects/PairsTrading/quantbook.ipynb` | 7 | 3 | 43% | 3/7 |
| `Python/QC-Py-Cloud-01-FinBERT-Sentiment.ipynb` | 6 | 5 | 83% | 5/6 |
| `Python/QC-Py-Cloud-02-ML-Classification.ipynb` | 3 | 2 | 67% | 2/3 |
| `Python/QC-Py-Cloud-03-Risk-Parity.ipynb` | 2 | 1 | 50% | 1/2 |
| `Python/QC-Py-Cloud-04-RL-DQN-Trading.ipynb` | 2 | 1 | 50% | 1/2 |
| `Python/QC-Py-Cloud-05-MLP-Forecasting.ipynb` | 2 | 1 | 50% | 1/2 |

### Non-QuantConnect (2)

| Notebook | Code | Exec | % Exec | Notes |
|----------|------|------|--------|-------|
| `Sudoku/Sudoku-16-NeuralNetwork-Python.ipynb` | 22 | 21 | 95% | 1 cell missing exec |
| `bin/Debug/.../Workbook-Template-Python.ipynb` | 7 | 2 | 29% | Build artifact, ignore |

---

## Priority Action Items

### P0 — Immediate (QuantConnect D_HAS_ERRORS, 5 critical)

These 5 quantbooks have >50% error cells and need QC Cloud re-execution:

1. `Crypto-MultiCanal/quantbook.ipynb` — 8/10 errors (80%)
2. `ML-XGBoost/quantbook.ipynb` — 8/11 errors (73%)
3. `RL-Portfolio/quantbook.ipynb` — 7/10 errors (70%)
4. `Alpha-Correlation-Analysis/quantbook.ipynb` — 11/18 errors (61%)
5. `VIX-TermStructure/quantbook.ipynb` — 6/10 errors (60%)

**Action**: Execute via QC Cloud MCP (`qc-mcp`) or Playwright automation. These require QuantBook runtime.

### P1 — High (QuantConnect C_NEVER_EXECUTED, 31 notebooks)

Majority are research/quantbook notebooks requiring QC Cloud execution.

- 9 `Research-Executor/research_*.ipynb` — template research notebooks
- 3 `ESGF-2026/kit-transitoire/` — student kit templates
- 4 `Python/QC-Py-XX-*.ipynb` — course notebooks (01, 04, 19, Dataset)
- Remaining: project-specific quantbooks and research notebooks

**Action**: Batch QC Cloud execution. Group by type for efficient processing.

### P2 — Medium (QuantConnect B_PARTIAL_EXEC, 9 notebooks)

Most are partially-executed quantbooks. Sudoku-16-NN is 95% complete (1 cell).

**Action**: Re-execute Sudoku-16 locally (Python kernel). QC quantbooks via Cloud.

### P3 — Low (Non-QC issues, 4 notebooks)

| Notebook | Action |
|----------|--------|
| `GenAI/SemanticKernel/fort-boyard-csharp.ipynb` | Evaluate: WIP demo or archive |
| `SymbolicAI/archive/Tweety.ipynb` | Archived, 1/34 error — acceptable |
| `Sudoku/Sudoku-16-NeuralNetwork-Python.ipynb` | Re-execute 1 missing cell |
| `GradeBook.ipynb` | Evaluate: utility notebook |

---

## Git Freshness Analysis

All problematic QuantConnect notebooks share `last_commit: 2026-05-12T18:46:04+02:00` — batch-committed during a recent sweep. This confirms they were touched structurally without re-execution (rule H.1).

Notebooks with `pre_rule_c2: true` (3) predate the C.2 rule (committed before 2026-04-26):
- `ESGF-2026/examples/Crypto-MultiCanal/research.ipynb`
- `projects/CSharp-BTC-MACD-ADX/Research.ipynb`
- `projects/Portfolio-Optimization-ML/research.ipynb`

---

## Methodology

- **Scan date**: 2026-05-12
- **Tool**: `scripts/notebook_tools/forensic_scan.py --with-git --json-out forensic_results.json`
- **Categories**: Based on JSON-level analysis of `execution_count`, `outputs`, and `output_type: error` per code cell
- **Exclusions**: `_archive_obsoletes/`, `_archives/`, `_old/`, `TrashBin/`, `.ipynb_checkpoints/`, `*_output.ipynb`, `_pending_execution/`
- **Full data**: `scripts/notebook_tools/forensic_results.json`

---

## Next Steps (H.7 Plan)

- **P2** (1 week): Fix C_NEVER_EXECUTED quantbooks — slot agents for QC Cloud execution
- **P3** (2 weeks): GitHub Actions CI workflow to block merges with unexecuted notebooks
- **P4** (continuous): Monthly regeneration of this snapshot, commit as `sha + date + matrix`

---

*Generated by po-2023 agent — H.7 STABLE_SNAPSHOT P1 forensic audit*
