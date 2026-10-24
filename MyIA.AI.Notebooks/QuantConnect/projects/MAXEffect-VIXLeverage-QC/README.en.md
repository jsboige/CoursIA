# MAXEffect-VIXLeverage-QC — long-only MAX effect with VIX-scaled leverage

English original of [README.md](README.md) (French is the primary documentation language of this repository).

Distillation of QC Research article 20886 "The MAX Effect with VIX-Based Leverage Scaling" (Derek Melchin, 2026-06-12), part of the `quantconnect.com/research` harvest (EPIC #11698, issue #22290, verdict **NOUVEAU** — no prior strategy in this repository carried the MAX effect).

## Idea

The **MAX(5)** factor of Bali, Cakici and Whitelaw (2011) [*Maxing Out: Stocks as Lotteries and the Cross-Section of Expected Returns*, Journal of Financial Economics 99(2), 427-446] takes, for each stock, the mean of its 5 largest daily returns over the last 21 sessions. High-MAX stocks behave like lottery tickets and **underperform** afterwards. This strategy sells that lottery — long-only:

- universe: filtered US equities (price > $5, market cap > $1B, average dollar volume > $5M, no REITs, no ADRs);
- **bottom** decile of the MAX factor, capped at 25 names, equal-weighted;
- monthly rebalance (first trading day of the month, 8:00 ET);
- VIX-driven leverage overlay: 1.5x when VIX <= 15, linearly down to 1.0x at VIX >= 30, rescaled continuously between rebalances (proportional rescale, relative weights unchanged).

The article reports Sharpe 0.57 (1998-01 -> 2026-06) versus 0.335 for SPY, with 25/25 parameter-sweep configurations beating their benchmark.

## Lag convention

The day-D VIX close is only delivered at D+1 (`CBOE.lag_days = 1`), the repository convention since the anti-lookahead measurements #19825/#19837: reading the same-day close at decision time is a lookahead. The VIX is loaded through a local `CBOE(PythonData)` class reading the public CBOE CDN CSV (the .NET namespace `QuantConnect.Data.Custom.CBOE` cannot be imported from a Python algorithm on QC Cloud).

## Measurements — QC Cloud, 2026-10-24 (project 38366686)

Window 2015-01-01 -> 2026-06-30, $100k, zero risk-free rate Sharpe, three modes from a single project:

| Mode | Description | Sharpe | CAGR | Max drawdown | Backtest |
|---|---|---|---|---|---|
| `max-vix` | candidate (factor + VIX overlay) | 0.181 | 5.402% | 26.400% | `47d6ad9479ee72e8d8fda2e6fd6d8cd7` |
| `max-only` | ablation (factor only, 1.0x) — in flight | — | — | — | `3158bd546830303dc013f8763faf3b98` |
| `spy` | held reference (SPY buy-and-hold) | 0.551 | 13.739% | 33.500% | `b36253509d96547fb0b98baf8a1187eb` |

Candidate total: +83.16% ($100,000 -> $183,163.72); held SPY total: +339.68% ($100,000 -> $439,682.65).

**Session counter.** QC reports 4,199 "tradeable dates" for the two universe runs (candidate and ablation) against 2,889 for SPY. The 2015-01-01 -> 2026-06-30 window holds about 2,890 trading sessions, which makes 2,889 coherent and 4,199 uninterpretable as a count of calendar sessions: the universe runs' counter does not carry the same semantics. The figures compared here are the CAGR and Sharpe QC publishes over the same calendar window; a Sharpe comparison whose declared session counts differ is not a comparison on a proven identical window, and that limit is held against the result, not in its favour.

**Verdict: NO BEATS.** Over the measured window the candidate does not beat the held reference, in Sharpe (0.181 vs 0.551) nor in CAGR (5.40% vs 13.74%). One point runs the other way and is stated: the candidate's drawdown is lower than SPY's (26.40% vs 33.50%), the expected effect of the leverage overlay — less loss, but also less return. The candidate's return is carried by a single sub-window (2019-2022: 12.19% CAGR) while 2015-2018 is nearly neutral (0.79%) and 2023-2026-06 is weak (3.22%). The `max-only` ablation will decompose the absence of edge: whether the MAX factor alone carries anything, and whether the VIX overlay adds or removes. The daily Sharpe gap with circular block bootstrap and Holm correction is computed once all three runs are measured; it cannot flip the sign of a 0.37 Sharpe gap, it will bound its uncertainty.

### Article claims confronted

The article announces Sharpe 0.57 over 1998 -> present against 0.335 for held SPY. This port measures 2015 -> 2026-06 (the cluster's window convention), so the confrontation bears on the **verdict** — does it beat the held reference on the same window, with the same fees? — not on the Sharpe level. The 0.181 measured over 2015-2026 already sits clearly below the article's 0.57 over a longer window, which suggests the claimed edge eroded over the recent period; the ablation (factor only, fixed 1x leverage) will say whether the erosion lives in the MAX factor or in the VIX overlay.

## Structure

- `main.py` — `MAXEffectVIXLeverage(QCAlgorithm)`, `mode` parameter in {`max-vix`, `max-only`, `spy`}; MAX(5)/21-session factor in `SelectionData` (canonical QC tutorial pattern), local `CBOE(PythonData)` class at the bottom.
- Exposed parameters: `top_returns` (5), `max_portfolio_size` (25), `period` (21), `low_vix` (15), `high_vix` (30), `low_leverage` (1.5), `high_leverage` (1.0).

Related reading: [docs/qc/qc-strategies-status.md](../../../../docs/qc/qc-strategies-status.md) — repository strategy status.
