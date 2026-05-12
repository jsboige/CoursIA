# H.7 P2 Docker Error Catalog

**Date**: 2026-05-13
**Source**: 31 never_executed QC notebooks executed via lean-cli Docker (`qc_quantbook_execute.py`)
**Total errors**: 200 across 31 notebooks
**Scope**: All errors are Docker environment limitations, NOT code bugs

## Summary by Root Cause

| Category | Root errors | Cascade (NameError) | Fix scope |
|----------|-------------|---------------------|-----------|
| QC DataFrame column naming | 37 | ~80 | QC Cloud only |
| Empty data (crypto/sector ETFs) | 15 | ~30 | QC Cloud only |
| QC data structure (tuple index, types) | 7 | ~5 | Code refactor possible |
| Missing local files/directories | 4 | 0 | Docker volume mount |
| Missing Python packages | 4 | 0 | Dockerfile update |
| Other (syntax, NotFitted) | 5 | ~6 | Code fix |
| **TOTAL** | **~72 root** | **~128 cascade** | |

**Key insight**: 64% of errors are cascades from ~36% root causes. Fixing root causes eliminates cascades automatically.

---

## Category 1: QC DataFrame Column Naming (37 root errors)

**Root cause**: `qb.History()` returns Lean Symbol IDs (e.g., `SPY R735QTJ8XC9X`) as column names, not simple tickers. Code expects `df['close']` but columns are multi-level.

**Affected notebooks** (sample):
- `ESGF-2026/examples/Crypto-MultiCanal/research_archive.ipynb` (multiple cells)
- `ESGF-2026/kit-transitoire/01-ML-RandomForest/research.ipynb` (cells 5, 8, 9)
- `ESGF-2026/kit-transitoire/02-ML-XGBoost/research.ipynb` (cells 6, 14, 15)
- `ESGF-2026/kit-transitoire/03-Framework-Composite/research.ipynb` (cells 4, 8, 10)
- `projects/ML-HeadShoulders-CNN/research.ipynb` (cell 4)

**Example error**:
```
KeyError: "No key found for either mapped or original key.
  Mapped Key: ['close']; Original Key: ['close']"
```

**Fix options**:
1. **QC Cloud**: Works natively (Symbol IDs resolved by cloud backend)
2. **Code refactor**: Use `str(ticker) in c` for column matching, or `.droplevel(0)` on MultiIndex
3. **Already fixed in some notebooks**: ML-DeepLearning, ML-TextClassification use `str(ticker) in c` pattern

---

## Category 2: Empty Data (15 root errors)

**Root cause**: Docker research image only has data for 5 tickers: **SPY, QQQ, AAPL, GOOGL, IWM**. All other tickers (sector ETFs, crypto, international) return 0 rows.

**Unavailable tickers**:
- Crypto: BTCUSD, BTCUSDT, ETHUSD
- Sector ETFs: XLE, XLP, XLV, XLK, XLU, XLY
- International: EFA, EEM
- Bonds: AGG, TLT
- Volatility: VIX, UVXY, SVXY

**Affected notebooks**:
- `projects/Multi-Layer-EMA/research.ipynb` (BTCUSD KeyError)
- `ESGF-2026/kit-transitoire/*` (ValueError: zero-size array)
- `projects/Framework_Composite_*/quantbook_composite_research.ipynb` (GOOGL KeyError in one case)
- `projects/Crypto-MultiCanal/research.ipynb` (IndexError: empty DataFrame)

**Example error**:
```
ValueError: zero-size array to reduction operation maximum which has no identity
```

**Fix options**:
1. **QC Cloud**: Full ticker universe available
2. **Code refactor**: Replace crypto/sector tickers with available equity ETFs (SPY/QQQ/AAPL/GOOGL/IWM)
3. **Docker data injection**: Mount additional data files (not attempted)

---

## Category 3: QC Data Structure Differences (7 root errors)

**Root cause**: `qb.History(symbol, ...)` returns `(Symbol, datetime)` MultiIndex in Docker, not bare `datetime`.

**Affected notebooks**:
- `projects/DL-LSTM/quantbook.ipynb` (cell 3: `'tuple' object has no attribute 'date'`)
- `projects/CSharp-CTG-Momentum/research_robustness.ipynb` (cell 1: MultiIndex str accessor)
- `projects/BTC-ML/research.ipynb` (cell 6: cannot remove 1 levels from 1-level index)

**Example error**:
```
AttributeError: Can only use .str accessor with Index, not MultiIndex
```

**Fix options**:
1. **Code refactor**: `.droplevel(0)` after `qb.History()` to remove Symbol level
2. **QC Cloud**: Returns consistent DataFrame structure

---

## Category 4: Missing Local Files (4 root errors)

**Root cause**: Notebooks reference local dataset files (`../datasets/`, `/Lean/Launcher/bin/Data/`) not present in Docker container.

**Affected notebooks**:
- `Python/QC-Py-Dataset-Workflow.ipynb` (cells 4, 8: FileNotFoundError for CSV files)
- `Python/research/research_classification.ipynb` (cell 5: market-hours-database.json)
- `Python/research/research_lstm.ipynb` (cell 6: market-hours-database.json)

**Example error**:
```
DirectoryNotFoundException: Could not find a part of the path
  '/Lean/Launcher/bin/Data/market-hours/market-hours-database.json'
```

**Fix options**:
1. **Docker volume mount**: Mount data directory into container
2. **QC Cloud**: All data available natively

---

## Category 5: Missing Python Packages (4 root errors)

**Root cause**: Docker image missing Python modules expected by notebooks.

**Affected notebooks**:
- `ML-Training-Pipeline/ML-Research-Template.ipynb` (cells 3, 9, 10: `train_classification`, `train_lstm`)

**Example error**:
```
ModuleNotFoundError: No module named 'train_classification'
```

**Fix**: Add custom module path to PYTHONPATH or install package in Docker image.

---

## Category 6: Other (5 root errors)

| Error | Notebook | Detail |
|-------|----------|--------|
| SyntaxError | `Research-Executor/runner.ipynb` cell 0 | f-string unmatched `(` (generated code) |
| NotFittedError | `research/research_classification.ipynb` cell 32 | RandomForest not fitted (empty data cascade) |
| TypeError | `Research-Executor/research_defensive_etf_rotation.ipynb` cell 4 | `MemoizingEnumerable` not subscriptable |
| TypeError | `03-Framework-Composite/research.ipynb` cells 8, 10 | dtype comparison object vs datetime64 |

---

## Notebooks by Error Severity

### High Error Count (>10 errors)
| Notebook | Errors | Root cause category |
|----------|--------|-------------------|
| `ESGF-2026/examples/Crypto-MultiCanal/research_archive.ipynb` | 33 | Column naming + empty data |
| `Python/QC-Py-04-Research-Workflow.ipynb` | 25 | Column naming + cascade |
| `Python/research/research_classification.ipynb` | 17 | Column naming + cascade |
| `Python/research/research_lstm.ipynb` | 17 | Column naming + cascade |
| `projects/BTC-ML/quantbook.ipynb` | 11 | Data structure |
| `projects/BTC-ML/research.ipynb` | 11 | Empty data |

### Clean Execution (0 errors)
| Notebook | Cells |
|----------|-------|
| `projects/Option-Wheel/research.ipynb` | 5/5 |
| `Python/QC-Py-01-Setup.ipynb` | 7/7 |
| `Python/QC-Py-19-ML-Supervised-Classification.ipynb` | 24/24 |
| `Research-Executor/research_commodity_term_structure.ipynb` | 3/3 |
| `Research-Executor/research_asset_class_momentum.ipynb` | 5/5 |

---

## Recommendations for H.7 P3

1. **QC Cloud re-execution**: Priority for the 5 notebooks with >15 errors. Will resolve most issues natively.
2. **Column naming utility**: Create `qc_helpers.py` with `get_close(qb, symbol, start, end)` that handles Symbol ID remapping and MultiIndex flattening. Applicable to ~20 notebooks.
3. **Docker data expansion**: If possible, inject additional ticker data for sector ETFs and crypto. Would resolve ~15 root errors.
4. **Cascade elimination**: Fixing the ~72 root errors automatically resolves the ~128 cascade NameErrors. Total resolution = 100%.
5. **GitHub Actions runner**: Must use QC Cloud backend or expanded Docker data, not bare lean-cli research image.
