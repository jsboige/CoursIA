# QC Cloud Organization Audit - April 2026

**Date**: 2026-04-28
**Scope**: All 134 projects across 3 organizations
**Author**: po-2024 (automated audit)

---

## Summary

| Metric | Value |
|--------|-------|
| Total projects | 134 |
| Org d600793e (Trading Firm ESGF) | ~50 |
| Org 94aa4bcb (Researcher) | ~4 |
| Org dc6b9eb0 (ECE Students) | ~80 |
| Active strategies (best Sharpe) | 12 |
| HandsOn book examples | 19 |
| Composites | 2 |
| HandsOn teaching | 2 |
| Clones of public strategies | ~8 |
| ESGF student projects | ~16 |
| Cleanup candidates | ~15 |

---

## Strategy Performance Rankings

Best completed backtest per strategy, ranked by Sharpe ratio:

| # | Strategy | Project ID | Best Version | Sharpe | CAGR | MaxDD | Net Profit | Date |
|---|----------|-----------|-------------|--------|------|-------|------------|------|
| 1 | EMA-Cross-Alpha | 28885488 | Final-Test | 0.996 | 33.3% | 44.1% | +2407% | 2026-03-11 |
| 2 | BlackLitterman-Momentum | 29816300 | v2-lower-vol-sma-filter | 0.823 | 15.7% | 16.9% | +398% | 2026-04-28 |
| 3 | Composite EMA50/Trend50 | 28911253 | Measured Green Leopard | 0.867 | 19.2% | 25.5% | +335% | 2026-03-12 |
| 4 | MeanReversion | 30776121 | v5.2 RSI65/stop10/RS | 0.810 | - | - | - | 2026-04-28 |
| 5 | TrendStocks-Alpha | 28885507 | v2 (2015+) | 0.718 | 18.2% | 33.7% | +551% | 2026-03-11 |
| 6 | VolTarget-Momentum | 30784745 | v6 vol18 wider | 0.652 | 15.4% | 21.3% | +404% | 2026-04-28 |
| 7 | DualMomentum | 28692516 | v8 regime-switching | 0.600 | 12.8% | 21.3% | +274% | 2026-04-28 |
| 8 | GlobalMacro-Regime | 30781695 | v3 rank-rp | 0.607 | 11.5% | 27.4% | +216% | 2026-04-28 |
| 9 | Trend-Following AQR | 28797562 | v8 regime-aware risk-parity | 0.566 | 10.7% | 22.0% | +196% | 2026-04-28 |
| 10 | Composite FF/AW | 30747169 | FF20/AW80 | 0.558 | 7.2% | 13.1% | +213% | 2026-04-27 |
| 11 | Composite MomentumRegime | 30748886 | T0/RS100 pure regime | 0.538 | 11.9% | 27.4% | +258% | 2026-04-27 |
| 12 | RiskParity-v2 | 30780629 | v4 rank-rp | 0.515 | 10.0% | 20.1% | +196% | 2026-04-28 |
| 13 | Sector-ML | 29318875 | v6.1 RF+SMA200 | 0.505 | 12.3% | 33.1% | +272% | 2026-04-28 |
| 14 | RiskParity (original) | 28692653 | extended | 0.399 | 7.8% | 20.9% | +132% | 2026-03-05 |
| 15 | Chronos-Foundation | 29443479 | v2 sma200-regime | 0.253 | 6.3% | 22.4% | +95% | 2026-03-28 |
| 16 | Corrective-AI | 30800636 | v1 | -0.151 | 2.2% | 11.3% | +17% | 2026-04-28 |
| 17 | RL-Options-Hedging | 30800109 | v2 | -3.612 | -0.8% | 6.3% | -6% | 2026-04-28 |

---

## Verdict by Project

### A jour (active, best version deployed)

| Project ID | Name | Best Sharpe | Last Backtest | Verdict |
|-----------|------|------------|---------------|---------|
| 30776121 | MeanReversion | 0.810 | 2026-04-28 | **a_jour** |
| 29816300 | BlackLitterman-Momentum | 0.823 | 2026-04-28 | **a_jour** |
| 30784745 | VolTarget-Momentum | 0.652 | 2026-04-28 | **a_jour** |
| 28692516 | DualMomentum | 0.600 | 2026-04-28 | **a_jour** |
| 30781695 | GlobalMacro-Regime | 0.607 | 2026-04-28 | **a_jour** |
| 28797562 | Trend-Following AQR | 0.566 | 2026-04-28 | **a_jour** |
| 30747169 | Composite FF/AW | 0.558 | 2026-04-27 | **a_jour** |
| 30748886 | Composite MomentumRegime | 0.538 | 2026-04-27 | **a_jour** |
| 30780629 | RiskParity-v2 | 0.515 | 2026-04-28 | **a_jour** |
| 29318875 | Sector-ML | 0.505 | 2026-04-28 | **a_jour** |

### Perime (working but superseded by better version in another project)

| Project ID | Name | Sharpe | Superseded By | Verdict |
|-----------|------|--------|---------------|---------|
| 28692653 | RiskParity (original) | 0.399 | 30780629 (RiskParity-v2, 0.515) | **perime** |
| 29443479 | Chronos-Foundation | 0.253 | Sector-ML (0.505) | **perime** |
| 28885488 | EMA-Cross-Alpha | 0.996 | Teaching demo only | **archive** |
| 28885507 | TrendStocks-Alpha | 0.609 | Teaching demo only | **archive** |
| 28911253 | Composite EMA50/Trend50 | 0.867 | Teaching demo only | **archive** |

### Research / Teaching (HandsOn book examples)

| Project ID | Name | Status | Chapter | Verdict |
|-----------|------|--------|---------|---------|
| 30800636 | Corrective-AI (Ch08-02) | 1 backtest, Sharpe -0.151 | Ch08 | **a_jour** |
| 30800109 | RL-Options-Hedging (Ch07-01) | 2 backtests, Sharpe -3.612 | Ch07 | **a_jour** |

These are HandsOn book examples (Issue #143). Negative Sharpe expected for ML exploration notebooks.

### Clones of Public Strategies (keep for reference)

| Project ID | Name | Source | Verdict |
|-----------|------|--------|---------|
| 28885488 | EMA-Cross-Alpha | Clone of EMA cross demo | **keep** (teaching) |
| 28885507 | TrendStocks-Alpha | Clone of trend demo | **keep** (teaching) |
| 28911253 | Composite EMA50/Trend50 | Composite demo | **keep** (teaching) |

### ESGF Student Projects (~16 projects)

ESGF teaching projects in org dc6b9eb0. Not audited here (student work).

### Cleanup Candidates

Projects with zero completed backtests, runtime errors only, or abandoned:

| Criteria | Count | Action |
|----------|-------|--------|
| 0 backtests (empty projects) | ~5 | Delete or keep if recent |
| All backtests Runtime Error | ~8 | Investigate or delete |
| Legacy (2018, pre-reorg) | 2 | Archive |
| Abandoned experiments | ~5 | Delete after confirmation |

---

## Recommendations

### Immediate Actions

1. **Delete empty projects** (0 backtests, no code changes) — saves org clutter
2. **Archive legacy projects** (2018 vintage) — move to "Archive" naming convention
3. **Keep all active strategies** — they are up-to-date as of 2026-04-28

### User Decisions Required

1. **RiskParity (28692653)**: Superseded by RiskParity-v2 (30780629). Delete original?
2. **Chronos-Foundation (29443479)**: 0.253 Sharpe, many runtime errors. Keep for reference or delete?
3. **Sector-ML runtime errors**: 12+ Runtime Error backtests. Clean up failed attempts?
4. **ECE student projects (dc6b9eb0)**: Audit separately?

### Strategy Health Check

| Status | Count | Strategies |
|--------|-------|-----------|
| Strong (Sharpe > 0.7) | 4 | EMA-Cross, BL-Momentum, Composite EMA/Trend, MeanReversion |
| Good (Sharpe 0.5-0.7) | 6 | VolTarget, DualMomentum, GlobalMacro, TrendFollowing, FF/AW, MomRegime, RiskParity-v2, Sector-ML |
| Weak (Sharpe < 0.5) | 3 | RiskParity (original), Chronos, Corrective-AI |
| Negative | 1 | RL-Options-Hedging (research) |

---

## Methodology

- Data collected via QC MCP `list_backtests` with `includeStatistics=true`
- All dates UTC, last backtest date used
- Sharpe ratio = best completed backtest per project
- Runtime Error backtests excluded from best-Sharpe selection
- 17/134 projects fully audited (all active strategies + key reference projects)
- ECE student projects (org dc6b9eb0, ~80 projects) not individually audited

---

*Generated by po-2024 on 2026-04-28 for Issue #558*
