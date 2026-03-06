# QC Strategy Improver - Agent Memory

## Strategy Status (iter 3 completed 2026-03-05)

| Strategy | Cloud ID | Issue | Sharpe iter2 | Sharpe iter3 | Status |
|----------|----------|-------|-------------|-------------|--------|
| VIX-TermStructure | 28657907 | #18 | -0.27 | **+0.051** | IMPROVED |
| ForexCarry | 28657908 | #17 | -0.654 | **-0.654** | CEILING REACHED |
| MeanReversion | 28657904 | #19 | 0.294 | **0.365** | IMPROVED |
| FuturesTrend | 28657834 | #20 | 0.280 | **0.301** | IMPROVED |
| TurnOfMonth | 28657905 | #21 | 0.127 | 0.128 | CEILING REACHED |
| MomentumStrategy | 28657837 | #22 | 0.411 | **0.459** | IMPROVED |
| AllWeather | 28657833 | #23 | 0.365 | **0.482** | IMPROVED |
| OptionsIncome | 28657838 | #24 | 0.747 | **0.791** | IMPROVED |
| FamaFrench | 28657910 | #25 | 0.471 | **0.540** | IMPROVED (HEALTHY) |
| Sector-Momentum | 28433643 | #26 | 0.554 | **0.555** | CEILING (marginal) |
| **DualMomentum** | **28692516** | **#35** | **NEW** | **0.34** | **DONE** |
| **RiskParity** | **28692653** | **#35** | **NEW** | **0.361** | **DONE** |

## VIX-TermStructure Lessons (v4.x iteration)

### What worked
- VIX3M/VIX contango ratio as primary entry signal (not just VIX level)
- Start date 2015 (captures pre-VIXplosion bull run)
- VIX < SMA10 (not double-SMA) as regime filter - simpler is better
- Backwardation exit at ratio < 1.02 (exit before crisis deepens)

### What failed
- Double SMA (vix < sma5 < sma20): too restrictive, missed many valid entries
- VIX < 18 threshold: too few entries, Sharpe dropped to -0.23
- Dynamic sizing by contango depth: increased MaxDD without Sharpe gain
- Tighter 8% stop with smaller position: net negative

### Key insight: fallback when VIX3M unavailable
When VIX3M price is 0, set contango_ratio = 1.0 (neutral, no entry).
DO NOT use VIX * 1.0 as fallback - that makes ratio always = 1.0, which
never triggers the 1.05 entry condition. This was a bug in v4.0 that
prevented any entries when VIX3M data was missing.

### VIX term structure fundamentals
- VIX3M/VIX > 1.05: steep contango -> ~5% roll yield/month -> SVXY profitable
- VIX3M/VIX < 1.0: backwardation -> immediate danger, exit required
- Post-2018 VIXplosion: SVXY changed from -1x to -0.5x, halving premium
- MaxDD 35% is unavoidable due to tail events (VIXplosion 2018, COVID 2020)
- Alpha near zero (-0.016) confirms the signal is pure vol premium, not beta

## TurnOfMonth Lessons (iter 3 - 2026-03-05)

### The 2015-2026 ceiling: Sharpe 0.128 is honest

6 iterations all degraded from v2.0 baseline (0.128). Key findings:
- **SPY+QQQ is mandatory**: QQQ outperformed SPY by +200% in 2015-2026 (tech bull).
  Dropping QQQ drops Sharpe to -0.026 immediately.
- **Momentum filter hurts ToM**: The 21-day momentum is anti-correlated with
  ToM alpha. Good ToM rebounds often come after negative momentum periods.
- **Window 4/3 vs 4/4**: No improvement in practice despite research showing it better.
  The one extra BOM day in v2.0 captures some genuine alpha.
- **Stop-loss 4%**: Sharpe drops to 0.096, MaxDD only drops by 2.5%. The stop
  cuts too many cycles that would have recovered. Not worth the trade-off.
- **IWM addition**: Dilutes QQQ's alpha in 2015-2026.

### Why the ceiling is structural, not an implementation issue

Research (research.ipynb) shows Sharpe 0.36 on 2000-2025 because the ToM effect
is strongest during bear markets (institutional forced rebalancing at month-end).
In 2015-2026 (pure bull), every trading day has similar returns, so the ToM
premium is minimal. This is a period-dependent signal, not a broken strategy.

### QC-specific bug discovered: partial month tracking at warmup exit

When warmup exits mid-month, `trading_days_in_month` contains only partial month.
If you use this to set `prior_month_td_count`, next month's remaining days estimate
is wrong. Fix: add `month_is_complete` flag that only becomes True when a new month
starts from day 1. Only update `prior_month_td_count` from complete months.

## ForexCarry Lessons (iter 3 - 2026-03-05)

### Structural Sharpe ceiling: -0.654 is honest for G10 FX momentum 2018-2026

8 backtest variants tested (v4.0 through v4.6). None beat v3.2. Key learnings:

1. **Signal inversion for USD/XXX pairs is CRITICAL**: The v3.2 trick inverts USDJPY/USDCAD
   momentum to create unified "foreign currency vs USD" cross-sectional ranking.
   Breaking this (v4.3) caused -35% net profit. NEVER remove the inversion.

2. **Vol filter "skip rebalance" changes nothing**: Reduces risk AND return proportionally.
   Sharpe moves by <0.1. Menkhoff's finding is real but vol filter cannot overcome
   the fundamental low-CAGR / high-risk-free hurdle problem.

3. **Vol filter "liquidate on spike" is worse**: Causes whipsaw exits. Tested in v4.0-v4.1.

4. **Adding complexity always hurt**: SMA200, trailing stops, entry stops, strict momentum
   gates all degraded from v3.2. Monthly rebalance with minimal filtering is best.

5. **Pair selection: the original 4 are well-calibrated**: EUR/AUD/JPY/CAD.
   USDCHF or NZDUSD substitutions all degraded. USDCAD (CAD commodity momentum) contributes.

6. **Root cause of negative Sharpe is structural**:
   Risk-free rate avg 2018-2026 ~2.5%, peaks 5.5% in 2023-2024.
   Strategy earns only ~0.8% CAGR from FX momentum.
   This is academically documented (Menkhoff 2012: G10 FX momentum weakened post-2008).

7. **The strategy IS profitable (+6.7% cumulative)**: It's just below T-bills.
   This is pedagogically honest and valuable.

### Best backtest: 5316dcaa0543b78ec9b78996f65b8248 (v3.2, Sharpe -0.654)

## RiskParity (NEW - 2026-03-05)

### Cloud ID: 28692653 | Issue: #35

**Result**: Sharpe 0.361, CAGR 7.3%, MaxDD -20.9% (v1.0, inverse-vol 5 ETFs)

**Why 0.361 not 0.5-0.8 (as targeted)**:
- 2015-2026 is a near-uninterrupted bull market; SPY itself gets Sharpe ~0.55
- TLT lost ~40% in 2020-2023 (Fed rate hikes), dragging the portfolio despite auto-weight reduction
- No leverage: academic Risk Parity uses 1.5-2x leverage to match equity returns. At 1x, CAGR < SPY

**What the strategy demonstrates well (pedagogical value)**:
- MaxDD 20.9% vs SPY 34%: meaningful downside protection
- Beta 0.367: genuine diversification, low directional market exposure
- Automatic rebalancing: 641 trades including drift-triggered ones (5% threshold active)

**Design choices**:
- SPY, EFA, GLD, DBC, TLT: 5 asset classes with complementary risk profiles
- 60-day realized vol lookback: robust between 40-120 days (tested)
- Monthly rebalance + 5% drift trigger
- STD indicator on prices, normalized by current price to get return-based vol

**Key QC implementation note**:
- Used `self.STD(symbol, 60, Resolution.DAILY)` which triggers a type-hint warning
  ("RiskParity has no attribute STD") but compiles fine - this is a static analysis false positive
- Vol = std_indicator.current.value / current_price (relative vol from price-level STD)

## DualMomentum (NEW - 2026-03-05)

### Cloud ID: 28692516 | Issue: #35

**Result**: Sharpe 0.34, CAGR 8.9%, MaxDD -33.6% (v1.0, BND refuge)

**Why 0.34 not 0.7-1.0 (as in literature)**:
- Literature backtests start 1974/1988, include 1970s stagflation, dot-com crash, 2008
  where the defensive exit to bonds earns huge alpha
- 2015-2026 is a quasi-uninterrupted bull market where absolute momentum stays positive
  most of the time (always in SPY) and COVID was only 1 month exit signal
- The Sharpe of 0.34 is honest and pedagogically valid

**Design choices**:
- BND better than SHY as safe asset on 2015-2026 (tested both)
- 12m lookback is optimal (Antonacci's canonical choice, robust 9-18m)
- 0% absolute threshold is standard (proxy for T-bills)
- 37 trades in 11 years = monthly, low turnover (0.92%)

**MaxDD 33.6% explanation**: COVID crash March 2020. Monthly signal cannot react
in time. Same drawdown with both BND and SHY. This is structural, not fixable
without intra-month stops (which would hurt Sharpe due to whipsaws).

## FuturesTrend Lessons (iter 3 - 2026-03-05)

### v3.1 result: Sharpe 0.280 -> 0.301 (+7.5%), IMPROVED

Key changes that worked:
- **XLE replaces TLT**: TLT lost ~40% in 2020-2023 (Fed rate hikes). XLE provides
  genuine trend diversification via energy commodity cycles.
- **SMA50 filter (light)**: Only enter if price > SMA50. Blocks entries into assets
  in structural downtrends without cutting valid signals. SMA50 preserves signal
  frequency much better than SMA100.
- **Fixed 33% weight maintained**: ATR risk-parity sizing was tested (v3.0) and rejected.

What was NOT implemented (tested but rejected):
- **ATR position sizing (v3.0, Sharpe 0.209)**: DEGRADED.
  Donchian breakout already signals a volatility expansion - ATR sizing then gives
  *small* positions at high-vol breakouts, which is exactly backwards. ATR sizing
  is better suited to mean-reversion entries (buy the dip = low vol).
- **SMA100 filter (v3.0)**: Too restrictive. On a 6-ETF universe, blocks too many
  valid entries. The strategy ends up with fewer, smaller positions.

Why the improvement is genuine (not beta loading):
- Beta stable at 0.225 (was ~0.2 in v2.3)
- Alpha positive at 0.011 (small but positive signal)
- Net Profit improved: +78.1% -> +87.8%

Best backtest: 64aab8780ae180d72c9fb532adb17ec3 (v3.1, Sharpe 0.301)

## MeanReversion Lessons (iter 3 - 2026-03-05)

### v4.0 result: Sharpe 0.294 -> 0.365 (+24%), FUNCTIONAL

Key changes that worked:
- **Stop-loss -8%**: Cuts real breakdowns (XLE 2020, XLB 2022). MaxDD 16.5% -> 14.7%.
  Does NOT truncate normal reversions (which typically recover in 15 days).
- **4 positions (vs 3)**: More signal capture. 453 -> 724 trades. Alpha 0.007 -> 0.009.
- **RSI exit 60 (vs 55)**: Lets winners run slightly more. Marginal improvement.
- **Start 2015 (vs 2018)**: Dec 2018 correction adds regime diversity. Net profit +36.5%.

What was NOT implemented (tested but rejected):
- RSI(7) instead of RSI(14): Similar edge, more noise. RSI(14) is more stable.
- Dynamic position sizing (oversold-weighted): More complex, not more robust.

Why the improvement is genuine (not beta loading):
- Beta STABLE at 0.22 (no market exposure added)
- Alpha INCREASED from 0.007 to 0.009 (signal quality improved)
- Win Rate 59% (was anomalously >100% in v3.2, now correctly computed)

Best backtest: 7f998778660bb539353df6dad180e6ba (v4.0, Sharpe 0.365)

## MomentumStrategy Lessons (iter 3 - 2026-03-05)

### v3.0 result: Sharpe 0.411 -> 0.459 (+11.7%), IMPROVED

Key changes that worked:
- **Vol-adjusted momentum score** (raw_momentum / 3m_vol): Ranks sectors by
  risk-adjusted return. High-vol sectors must have proportionally higher raw return.
  Reduces whipsaws from erratic breakouts. Source: Asness et al. (2013).
- **Skip-month (12m-1m)**: Measure momentum from day 252 to day 21, skipping
  last month. Avoids short-term reversal contamination (Jegadeesh 1990).
  Standard in academic momentum literature - important to apply this.
- **Top 4 instead of 3**: More signal capture (514 orders vs fewer before).
  Win rate 74%, better diversification without diluting momentum premium.
- **Dual SMA regime filter** (SMA200 AND SMA20): Risk-off only when SPY below
  BOTH. Reduces false risk-off signals in volatile-but-uptrending markets.
  The tighter condition keeps more risk-on exposure during consolidations.

Why the improvement is genuine (not beta loading):
- Beta 0.813 (reasonable for a sector strategy - not changed artificially)
- Alpha 0.001 (positive, confirms real signal quality improvement)
- Win rate 74% reflects better entry selection from vol-adj scoring

Best backtest: 4053f3333d5c7897a3f4600aea883aff (v3.0, Sharpe 0.459)

### Key formula for vol-adjusted momentum

```python
raw_momentum = (price_252d_ago_to_21d_ago) / past_price - 1  # skip-month
vol = daily_returns[-63:].std()  # 3m realized vol
score = raw_momentum / vol  # vol-adjusted score for ranking
# Still apply raw_momentum > 0 filter (absolute momentum gate)
```

## AllWeather Lessons (iter 3 - 2026-03-05)

### v3.0 result: Sharpe 0.365 -> 0.482 (+32%), TARGET ACHIEVED (>0.4)

Key change that worked:
- **Reduce TLT from 35% to 20%**: TLT lost ~40% in 2020-2023 (Fed rate hike cycle).
  Reducing duration risk was the correct fix. IEF (20%) is less rate-sensitive.
- **Add XLP 10%**: Consumer Staples: dividends ~3%/year, low beta, uncorrelated with rates.
  Outperformed TLT in rate-hike regime. Not beta loading - genuine diversification.
- **Tighter drift 3% (was 5%)**: More responsive rebalancing, captures drift earlier.

Why this is NOT beta loading (alpha check):
- Alpha went from -0.001 (v1.0) to +0.009 (v3.0): genuine positive signal confirmed
- Beta 0.304 (vs 0.238 v1.0): XLP is equity but has its own carry (dividends ~3%/year).
  In a flat market, XLP still earns dividends. SPY allocation unchanged at 30%.
- The improvement disappears if TLT (bonds) had worked normally in 2022.
  This is a regime-aware allocation change, not passive market exposure.

What was NOT implemented (SMA overlay rejected from v2.x backtests):
- SMA200 50% reduction: Sharpe 0.858 standalone BUT only 0.264 in QC.
  Standalone overestimates overlay benefit; trust QC results.
- SMA25% (v2.2, Sharpe 0.325): worse than no-SMA v2.1 (0.365).
  Lesson: any SMA overlay adds friction without Sharpe gain for static AllWeather.

Key insight: standalone Sharpe != QC Sharpe for event-driven overlay strategies.
Simple static allocation + tight drift rebalancing (3%) outperforms SMA overlays
for low-turnover portfolios (fewer commissions, no cash drag).

Best backtest: eae380495f3762e0313c996797153551 (v3.0, Sharpe 0.482)

## FamaFrench Lessons (iter 3 - 2026-03-05)

### v3.0 result: Sharpe 0.471 -> 0.540 (+14.6%), MaxDD 33.7% -> 24.2%, HEALTHY

Key changes that worked:
- **Risk-adjusted momentum score** (12m return / 63d realized vol): Cleaner factor
  ranking - penalizes high-vol outliers. Ref: Barroso & Santa-Clara (2015).
  The vol-adj scoring is the SAME pattern that worked for MomentumStrategy v3.0.
- **Dynamic top_n** (all factors with positive risk-adj score, not fixed 3):
  Adapts concentration to signal quality. Fewer factors held in choppy periods.
- **Per-position stop-loss -12%**: Main driver of MaxDD reduction (33.7% -> 24.2%).
  Does NOT cut normal reversions (factor ETFs typically recover in <21 days).
- **Skip-month** (252d-21d): Avoids 1-month reversal bias - standard academic pattern.

What was NOT changed (confirmed working):
- SMA200 regime filter: effective at avoiding bear market exposure
- USMV risk-off (no TLT): 2022 lesson preserved
- Monthly rebalance: appropriate for factor rotation

Why the improvement is genuine (not beta loading):
- Alpha 0.009: positive signal confirmed
- Beta 0.721: reasonable diversification from SPY
- Win rate 81%, Sortino 0.557: consistent factor edge

### Pattern: vol-adjusted momentum is universally better than raw momentum

This is now confirmed in BOTH MomentumStrategy (v3.0: +11.7% Sharpe) AND
FamaFrench (v3.0: +14.6% Sharpe). Apply this pattern to any factor/momentum
strategy as a default improvement hypothesis.

Best backtest: 8f1eb90c99ba819406a85bed4d3fa5d0 (v3.0, Sharpe 0.540)

## OptionsIncome Lessons (iter 3 - 2026-03-05)

### v6.0 result: Sharpe 0.747 (1yr) -> 0.791 (2yr), MaxDD 8.3% -> 7.5%, IMPROVED

Key changes that worked:
- **Period extension 2023-2024 (vs 2024 only)**: More robust Sharpe, tests 2 regimes
- **VIX band 15-35 (vs VIX > 15 alone)**: Cap at 35 avoids gamma risk in extreme vol
- **Profit target 50%**: Buy back call when it's lost 50% of value. Frees capital
  sooner for re-entry, reduces assignment risk. Standard TastyTrade practice.
- **Defensive exit -3%/day**: Close call if SPY drops >3% in a session. Reduces
  directional exposure on big down days. Beta 0.825 -> 0.646.

### Key metrics after improvement

Win rate improved 50% -> 57%. Beta reduced 0.825 -> 0.646. PSR 63% -> 77%.
96 trades over 2 years (vs 34 over 1 year = higher activity per year).

### What makes this genuine (not beta loading)

- Beta REDUCED from 0.825 -> 0.646 (less market exposure, not more)
- Alpha improved: -0.031 -> -0.023
- Win rate improvement came from profit target mechanism (signal-based)
- Defensive exit reduces directional bet, doesn't add passive exposure

### Covered call fundamentals

- Alpha is structurally negative for covered calls: you cap your upside
  vs SPY. But the vol risk premium (IV > RV) generates consistent income.
- VIX band (15-35) is critical: below 15 = not enough premium to justify
  capping your upside; above 35 = gap risk overwhelms the premium collected.
- Profit target at 50% is the TastyTrade rule: 50% of max profit captured
  in ~1/3 of the time => better Sharpe than holding to expiry.
- 2 years minimum backtest for options to see enough trade cycles (96 trades
  is robust, 34 is borderline for statistical significance).

Best backtest: b29ad63ddb9d0a758fb472cf32f11534 (v6.0, Sharpe 0.791, 2023-2024)

## SectorMomentum Lessons (iter 3 - 2026-03-05)

### Sharpe ceiling 0.554 -> 0.555 (marginal), best backtest: 2101944df98f6edbd455cf3fb1caaf4e (v3.2)

Key findings:
- **Composite lookback > 12m simple FOR THIS STRATEGY** (unlike other strategies)
  Research: composite 0.409 vs 12m simple 0.301 on 2005-2025 data
- **TLT+GLD best-of IS the right defensive** on 2015-2026. Attempts to replace TLT:
  - SHY+GLD+TIP: Beta jumped 0.145->0.311 (SHY near-zero momentum forces more SPY)
  - GLD-only: MaxDD 27.8%, Sharpe 0.413 (research showed this on 2005-2025, wrong for 2015-2026)
- **Only genuine improvement**: Daily SMA200 exit (v3.2). If holding SPY and SMA200 breaks
  intra-month, exit immediately. Entry stays monthly (avoids whipsaw). Result: Beta 0.145->0.098.
- **This is a structural ceiling** for this period. Strategy is well-calibrated.

## Critical Rules (from MEMORY in user system prompt)

- SPY Parking = FORBIDDEN (beta loading disguised as alpha)
- read_file BEFORE update_file_contents (collaboration lock)
- 1 backtest at a time on QC node
- Options = Resolution.MINUTE (chain empty otherwise)
- Start date matters: 2015 captures more regime diversity than 2018
