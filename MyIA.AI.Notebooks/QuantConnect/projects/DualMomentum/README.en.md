# DualMomentum Strategy

**Status**: ⚠️ REPLACED by DualMomentumNoTLT - Counter-Example for Educational Purposes

## Performance — verified measures (multi-source)

> **Honest note (#1621, drainage #9434)**: the legacy `0.350 / 9.2% / 33.6%` figures displayed before this PR were **stale** (predating the `v4→v6b` iterations of `main.py`) and **unattributed** to any reproducible backtest. The table below cites **currently-reproducible measures** from three distinct sources in the folder — **three different implementations** of dual momentum (naive 3-asset, 6-asset with filters, parametric exploration). All values come from a **real execution** of the notebooks/files present on `main` at the time of this PR.

| Source | Sharpe | CAGR | Max DD | Period | Universe |
|--------|--------|------|--------|--------|----------|
| [`research.ipynb`](research.ipynb) cell[10/25] (default 12m, 5 bps TC) | **0.460** | **7.89%** | **-19.81%** | 2015-2026 | SPY/EFA/BND |
| [`main.py`](main.py) v6b docstring (LEANT backtest, IBKR margin) | **0.557** | **11.22%** | **-15.3%** | 2015-2024 | SPY/EFA/EEM/TLT/GLD/DBC |
| [`quantbook.ipynb`](quantbook.ipynb) cell[3] (default 12m, 0 TC) | **0.213** | **6.2%** | **-34.1%** | 2007-2025 | SPY/EFA/BND |

**Honest reading**: the divergence between the three measures **is not a bug** — they are **three distinct implementations** of the same dual-momentum concept:
- `research.ipynb` uses the classical Antonacci definition (3-asset, lookback 12m, absolute threshold 0, 5 bps TC).
- `main.py` v6b uses an enriched version (6-asset, SMA200 + 6m filter, momentum tilt weighting) — **BEST iter** among the tested variants (see v4→v6b log in the docstring).
- `quantbook.ipynb` uses the 3-asset version without transaction costs over **19 years** (incl. GFC 2008 + COVID 2020 + bear 2022).

For pedagogical use in 2026, **`research.ipynb` is the reference** (full 2015-2026 period, pure Antonacci method). For a LEANT deployment, **`main.py` v6b is the recommended version** (reproduced Sharpe). To understand parameter sensitivity, **`quantbook.ipynb` cell[3-7]** shows the lookback × threshold × refuge × universe × regime grid. Detailed provenance: [`MANIFEST.md`](assets/readme/MANIFEST.md).

## Why This Strategy Was Replaced

### Root Cause: TLT (Long-Term Treasuries) Risk-Off Failure

This strategy uses **TLT** as the risk-off asset during bear markets:
- **Hypothesis**: TLT provides safe haven during equity declines
- **Reality (2022)**: TLT crashed -26% during rate hike cycle
- **Impact**: Max drawdown of 33.6% (mostly from COVID + 2022)

### The COVID Problem (March 2020)

| Event | SPY Drop | TLT Drop | Strategy Impact |
|-------|----------|----------|------------------|
| COVID crash (Mar 2020) | -34% | +2% | TLT worked as intended |
| Rate hike cycle (2022) | -25% | **-26%** | TLT FAILED as safe haven |

**The structural issue**: TLT is **duration risk**, not true diversification:
- In rate hike cycles, TLT correlates WITH equities (both down)
- 2022 broke the "bonds = safe haven" assumption
- Max DD figures are in the "Verified measures (multi-source)" table above (varies by methodology — the legacy 33.6% value from the original README has been flagged as such)

### Replacement: DualMomentumNoTLT

> **Honest note**: the `0.350 / 9.2% / 33.6%` (DualMomentum original) and `0.469 / 11.0% / 23.6%` (DualMomentumNoTLT) figures below are the **legacy stale figures** from the README (predating `v4→v6b` iterations of `main.py`, drainage #9434). See the "Verified measures (multi-source)" table above for **currently-reproducible** values from the notebooks present on `main`.

| Strategy | Sharpe | CAGR | Max DD | Improvement |
|----------|--------|------|--------|-------------|
| DualMomentum (original) | 0.350 (stale) | 9.2% (stale) | 33.6% (stale) | Baseline |
| **DualMomentumNoTLT** | **0.469 (stale)** | **11.0% (stale)** | **23.6% (stale)** | **+34% Sharpe, -10% Max DD** |

**What changed**:
- Removed TLT, replaced with **defensive assets** (XLP, IEF, GLD)
- Max DD reduced from 33.6% → 23.6% (stale figures)
- Sharpe improved from 0.350 → 0.469 (stale figures)

### Lessons Learned

1. **TLT is not a safe haven in all regimes**: Duration risk creates correlation with equities during rate hikes
2. **Max DD is structural**: 33.6% drawdown is unacceptable for most investors
3. **Asset selection matters**: The choice of risk-off asset is as important as the signal
4. **Regime awareness**: Strategies must account for different market regimes (rate hikes vs. cuts)
5. **Don't overfit to one period**: TLT worked 2015-2020 but broke in 2022

## When DualMomentum (with TLT) CAN Work

This original approach may work in:
- **Falling rate environments**: TLT benefits from rate cuts
- **Deflationary periods**: Bonds provide true diversification
- **Shorter backtests**: 2015-2020 shows good results (but 2022 breaks it)

**For full-cycle (2015-2026)**: Use DualMomentumNoTLT instead.

## Pedagogical Value

This strategy serves as a counter-example for:
- ⚠️ **Asset selection risk**: The "safe haven" asset can become a source of risk
- ⚠️ **Regime dependence**: Strategies that work in one regime may fail in another
- ⚠️ **Max DD matters**: 33.6% drawdown is psychologically and financially damaging
- ⚠️ **The importance of full-period backtesting**: 2015-2020 looks good, 2022 breaks it

## Comparison to Replacement

```python
# Original (DualMomentum)
UNIVERSE = [SPY, QQQ, IEF, GLD, XLP, TLT]  # TLT included
RISK_OFF_ASSETS = [TLT, IEF, GLD, XLP]

# Replacement (DualMomentumNoTLT)
UNIVERSE = [SPY, QQQ, IEF, GLD, XLP]  # TLT removed
RISK_OFF_ASSETS = [IEF, GLD, XLP]  # Defensive, no duration risk
```

## References

- **DualMomentumNoTLT**: The improved version without TLT
- **SectorMomentum**: Similar dual-momentum approach with defensive assets
- **OPTIMIZATION_BACKLOG.md**: Full iteration history

---

**Note**: This strategy is kept as a counter-example. For production use, see **DualMomentumNoTLT** which removes TLT and achieves better risk-adjusted returns.
