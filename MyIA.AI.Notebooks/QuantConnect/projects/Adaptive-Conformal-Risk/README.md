# Adaptive-Conformal-Risk

**Asset class:** US Equities/ETF (multi-factor)
**Cloud project IDs:** `29841071` (original, ECE-student no-fee 2015-2026) · `33278416` (`1630-baseline-AdaptiveConformalRisk`, IBKR + aligned 2018-2025)
**Source:** ECE student project (El Bakkali, Gr02), adapted for the ESGF pool — Issue #238.

## Description

Adaptive Conformal Inference (ACI) risk overlay on multi-factor momentum. Implements the ACI algorithm (Gibbs & Candès, 2021) as a dynamic risk-management overlay: online alpha-adjustment widens/narrows the conformal prediction interval in response to recent coverage violations, and position size is set inversely to the interval width — wider interval (more uncertainty) means a smaller position. Applied over a 15-stock, 5-sector large-cap universe with a 15% volatility target and monthly rebalancing.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Adaptive-Conformal-Risk"`
**QC Cloud:** Deployed (see Cloud project IDs above). The `main.py` committed here is the canonical copy with `set_brokerage_model(IBKR, MARGIN)` (real fees).

## Backtest Metrics

| Metric | Value | Window / fees |
|--------|-------|---------------|
| Method | ACI risk overlay + 3-window multi-factor momentum | — |
| Rebalance | Monthly (daily ACI alpha update) | — |
| Sharpe | **0.449** | 2018-2025, IBKR real fees (#1630-aligned) |
| CAGR | 11.5% | 2018-2025, IBKR |
| MaxDD | 22.5% | 2018-2025, IBKR |
| PSR | 12.5% (non-significant) | 2018-2025, IBKR |
| Sharpe (prior, no-fee) | 0.604 | 2015-2026, default fee model (negligible) |

**#1630 caveat (verified 2026-06-23).** Two findings: (a) the low-turnover monthly rebalance + ACI vol-targeting make the overlay **fee-resistant** (0.449 with IBKR is only modestly below the 0.604 no-fee figure, and much of that gap is the harder aligned window) — confirming the #1630 *realized-turnover* discriminator; (b) **but the universe is Mag7-heavy** (AAPL/MSFT/NVDA/AMZN/TSLA = 5 of 7 Mag7), so the Sharpe is substantially Mag7 survivorship drift rather than the marginal value of the conformal overlay (same caveat class as EMATrend). Full analysis: `docs/qc/qc-comparative-backtests.md` finding #38 (See #1630).

## Files

- `main.py` — Strategy (ACI overlay + multi-factor momentum, IBKR brokerage).

## References

- Gibbs, I. & Candès, E. (2021), *Adaptive Conformal Inference Under Distribution Shift*. (The ACI online-alpha algorithm implemented here.)
- Romano, Y., Patterson, E. & Candès, E. (2020), *Conformalized Quantile Regression*. (Conformal-prediction interval framework.)
