# QC Projects Consolidation Audit

**Issue**: #755
**Date**: 2026-05-06
**Author**: po-2025

## Summary

Audit of 4 non-canonical sources vs `projects/` (108 dirs, 99 with main.py):
- `projects-imported/` : 8 dirs
- `algorithms/python/` : 5 files
- `ESGF-2026/examples/` : 8 dirs
- `ESGF-2026/lean-workspace/` : 1 dir

**Result**: 14 SKIP, 7 MERGE, 0 NEW mandatory, 2 optional extractions.

---

## 1. projects-imported/ (8 dirs)

| # | Imported | Match in projects/ | Verdict | Lines I/P | Unique in imported |
|---|----------|-------------------|---------|-----------|-------------------|
| 1 | asset-class-momentum | AssetClassMomentum-QC | **SKIP** | 32/28 | None (hardcoded dates vs dynamic) |
| 2 | commodity-term-structure | TermStructureCommodities-QC | **SKIP** | 96/96 | None |
| 3 | defensive-etf-rotation | LeveragedETFMomentum-QC | **SKIP** | 131/200 | None (snake_case conversion of same QC ID) |
| 4 | long-short-harvest | LongShortHarvest-QC | **MERGE** | 691/624 | Bug fix: label threshold `> 1.02` vs `> 0.02` (L375) |
| 5 | macro-factor-rotation | MacroFactorRotation-QC | **MERGE** | 103/100 | 3 empty-data guard clauses |
| 6 | piotroski-fscore | HighBookToMarketFScore-QC | **SKIP** | 37/37 | None |
| 7 | puppies-of-dow | PuppiesOfTheDow-QC | **SKIP** | 69/46 | Minor `contains_key` guard |
| 8 | volatility-regime-ml | DynamicVIXSpyRegime-QC | **SKIP** | 246/259 | None (snake_case conversion of same QC ID) |

**Actions**:
- 6 SKIP directories to delete
- 2 MERGE: port bug fix + guards to projects/ versions, then delete

## 2. algorithms/python/ (5 files)

| # | Algorithm file | Match in projects/ | Verdict | Lines A/P | Unique |
|---|---------------|-------------------|---------|-----------|--------|
| 1 | AllWeatherPortfolio.py | AllWeather | **SKIP** | 416/115 | None (naive v1.0 vs evolved v5.0) |
| 2 | CoveredCallStrategy.py | OptionsIncome | **SKIP** | 421/195 | IronCondorStrategy class (low priority) |
| 3 | FuturesTrendFollowing.py | FuturesTrend | **MERGE** | 436/164 | MultiFuturesTrendFollowing (ES+GC+CL+ZB) |
| 4 | MomentumUniverseSelection.py | SectorMomentum | **SKIP** | 351/171 | None (universe selection pattern covered by QC docs) |
| 5 | MovingAverageCrossover.py | EMA-Cross-Stocks | **SKIP** | 338/73 | Advanced variant with volume filter (marginal) |

**Actions**:
- 4-5 files to delete
- 1 MERGE: extract MultiFuturesTrendFollowing to new project (optional)
- IronCondorStrategy: flag for future extraction (low priority)

## 3. ESGF-2026/examples/ (8 dirs)

| # | Example | Match in projects/ | Verdict | Lines E/P | Unique |
|---|---------|-------------------|---------|-----------|--------|
| 1 | BTC-MachineLearning | BTC-ML | **SKIP** | 337/375 | None (older variant) |
| 2 | Crypto-MultiCanal | Crypto-MultiCanal | **MERGE** | 423/379 | ChannelCalculationMixin + GA params |
| 3 | ETF-Pairs-Trading | ETF-Pairs | **SKIP** | 139/140 | None (nearly identical) |
| 4 | Multi-Layer-EMA | Multi-Layer-EMA | **SKIP** | 88/124 | None (older variant) |
| 5 | Option-Wheel-Strategy | Option-Wheel | **MERGE** | 133/110 | VIX filter + covered_puts.py + research notebooks |
| 6 | Options-VGT | Options-VGT | **SKIP** | 134/133 | None (nearly identical) |
| 7 | Sector-Momentum | SectorMomentum | **MERGE** | 46/125 | Different algo (dual momentum) + research notebooks |
| 8 | Trend-Following | Trend-Following | **MERGE** | 125/46 | Competition algo (600 equities) vs AQR-style (6 ETFs) |

**Actions**:
- 4 SKIP directories to delete
- 4 MERGE: evaluate unique content before deciding. Options:
  - Option-Wheel: merge VIX filter into projects/Option-Wheel
  - Sector-Momentum/Trend-Following: different enough to keep as separate variants in ESGF-2026/ (pedagogical context)
  - Crypto-MultiCanal: mixin architecture is alternative approach, keep for reference

## 4. ESGF-2026/lean-workspace/

| Entry | Verdict | Notes |
|-------|---------|-------|
| Multi-Layer-EMA-Researcher | **MERGE** | Variant with volatility filter + optimized params. Single orphan file. |

**Other cleanup targets**:
- `archive-2025/`: metadata-only, low risk
- `examples/Crypto-MultiCanal/fix_ipynb_quotes.py`: build artifact
- No numbered duplicates found

---

## Execution Plan

### Phase A — Bug fixes from imported sources (this PR)
- Fix `LongShortHarvest-QC/main.py` L375: `> 0.02` → `> 1.02`
- Fix `MacroFactorRotation-QC/main.py`: add 3 empty-data guards
- This audit document

### Phase B — Cleanup SKIP directories
- Delete `projects-imported/` (6 SKIP dirs, keep 2 MERGE for Phase C)
- Delete `algorithms/python/` (all 5 files after extraction)
- Delete `ESGF-2026/examples/` (4 SKIP dirs)
- Delete `ESGF-2026/lean-workspace/` after merging variant

### Phase C — Handle MERGE cases (DONE)

- `projects-imported/long-short-harvest` → DELETED (bug fix already in projects/)
- `projects-imported/macro-factor-rotation` → DELETED (guards already in projects/)
- `ESGF-2026/examples/Option-Wheel-Strategy` → DELETED (VIX filter already merged in projects/)
- `ESGF-2026/lean-workspace/Multi-Layer-EMA-Researcher` → DELETED (identical to projects/)
- `ESGF-2026/examples/Crypto-MultiCanal` → KEEP (different architecture: mixin + GA params + short trading)
- `ESGF-2026/examples/Sector-Momentum` → KEEP (different algo: alpha model framework + sector rotation)
- `ESGF-2026/examples/Trend-Following` → KEEP (different algo: competition 600 equities framework)
- `ESGF-2026/examples/generate_research_notebooks.py` → DELETED (build artifact)
- `projects-imported/` directory → now empty (removed)

### Phase D — Optional extractions
- MultiFuturesTrendFollowing → `projects/Multi-Futures-Trend/`
- IronCondorStrategy → `projects/Iron-Condor/` (low priority)

### Phase E — Post-cleanup
- README.md QC section: regenerate maturity table
- Convention: DRAFT/BETA/ALPHA entries need open issue or get deleted
- Validator extension: `scripts/validate_qc_projects.py`
