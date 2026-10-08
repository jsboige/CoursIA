# IchimokuEnergySector-QC — Ichimoku Clouds In The Energy Sector

QC Cloud port of QuantConnect research **9031 — "Ichimoku Clouds In The Energy Sector"**
(Derek Melchin, draft/pending review):
<https://www.quantconnect.com/research/9031/ichimoku-clouds-in-the-energy-sector/>.
French is the primary README (`README.md`); this is its English sibling.

- Grain: `DEEP/qc` — lane `myia-po-2023:CoursIA` — See #19678 (seed + acceptance), EPIC
  #11698 (QC-research harvesting).
- QC Cloud project: `IchimokuEnergySector-9031` (id 37468246), executed via the
  `quantconnect/mcp-server` MCP — never a fake local run.

## What the strategy does

The article applies the **Ichimoku Kinko Hyo** indicator to the top-10 energy-sector
market caps (monthly fine-fundamental universe, `MorningstarSectorCode.ENERGY`):

- the AlphaModel goes **long** when the **Chikou** line crosses the cloud top
  (Senkou A/B) from below, **short** when it crosses the cloud bottom from above;
- daily 1-day insights hold the position between crossovers;
- equal-weight portfolio construction, immediate execution, adjusted daily data.

The article confronts the strategy against the **XLE** benchmark (energy ETF) over four
windows and honestly concludes that **the strategy does not beat the benchmark** — exactly
what this port measures.

## Documented adaptations (a1-a6)

See `README.md` (French) for the full a1-a6 table — identical code on both sides.
Highlights: parametrized window/cash under IBKR fees (a1), an `xle_hold` comparator mode
sharing the exact same harness (a2), instance-level symbol data (a3), removed-symbol
cleanup (a4), explicit XLE benchmark (a5), and a typed `history[TradeBar]` warm-up
replacing the article's pandas pattern that throws `Runtime Error` on current LEAN (a6,
measured on first run).

## Reproduced metrics (IBKR fees, 1M cash)

### Strategy vs article — reproduction

The article publishes only two statistics per window (Sharpe and ASD) and defines **no**
out-of-sample window: 2015-01-01 → 2020-08-16 is both its tuning and its test period. Values
below are read from the source
(<https://www.quantconnect.com/research/9031/ichimoku-clouds-in-the-energy-sector/>, served as
HTML, no JavaScript).

| Window | Article — strategy (Sharpe / ASD) | Port — strategy (Sharpe / ASD) | Orders |
|---|---|---|---|
| Backtest 2015-01-01 → 2020-08-16 | -0.31 / 0.223 | not executed | — |
| Fall 2015 2015-08-10 → 2015-10-10 | -0.31 / 0.294 | **-2.504 / 0.053** | 848 |
| 2020 Crash 2020-02-19 → 2020-03-23 | 176.524 / 0.949 | **no trading at all** | **0** |
| 2020 Recovery 2020-03-23 → 2020-06-08 | -1.556 / 0.447 | not executed | — |

**The levels are not comparable, and this README does not pretend otherwise.** The article
publishes neither its starting capital, nor its fee model, nor its Sharpe aggregation
convention; the port runs under `BrokerageName.INTERACTIVE_BROKERS_BROKERAGE` (real per-share
fees, measured at 6.69 bps of traded volume on `fall2015`) with 1M cash. The `-2.504` vs
`-0.31` gap is **reported, not averaged** — those two numbers do not measure the same
experiment.

**The `2020 Crash` row is a port defect, not a result.** The article reports a Sharpe of
`176.524` there; the port trades **nothing** (0 orders, equity flat at 1,000,000 USD). A run
that does not trade neither confirms nor refutes the article. See "The computability wall"
below: the same signature has since been reproduced on four other windows, which rules out the
initial explanation ("23 sessions, too short to arm the universe").

### XLE buy-and-hold (same harness)

The comparator is the `xle_hold` mode of the **same project**: same bounds, same fees, same
calendar, same normalization. It is the only comparison this README treats as valid — a single
whole-position buy (1 order), hence no path dependence.

| Window | Source | Sharpe | ASD | Net | Max drawdown | Orders |
|---|---|---|---|---|---|---|
| Backtest 2015-01-01 → 2020-08-16 | article | -0.083 | 0.312 | — | — | — |
| Fall 2015 2015-08-10 → 2015-10-10 | article | 0.242 | 0.351 | — | — | — |
| 2020 Crash 2020-02-19 → 2020-03-23 | article | -0.902 | 1.108 | — | — | — |
| 2020 Recovery 2020-03-23 → 2020-06-08 | article | 46.068 | 0.703 | — | — | — |
| **Frozen block 2020-08-17 → 2026-09-30** | port | **0.746** | — | **+310.517 %** | 26.000 % | 1 |
| **Sub-window 2020-08-17 → 2022-08-16** | port | **1.276** | **0.290** | **+122.499 %** | 26.000 % | 1 |

The four "article" rows are the benchmark values published by the article, kept to situate the
order of magnitude; they are not replayed here. The two "port" rows are measured on this
repository (QC project `37468246`), and the `Sharpe` column is the harness's own field, read as
is — never substituted by ours (see the reproducibility caveat in `verdict_stats.py`).

**The baseline does not need splitting**: it completes on the whole frozen block, in one run,
with no seam. The 2026-10-08 measurement confirms it — the dedicated sub-window run
(1,000,000 → 2,224,992.87 USD) and the restriction of the full run's series give the same return
path, which is what a single whole-position buy must do: it has no dependence on the future.

### Out-of-sample extension (2020-08-17 → 2026-09-30)

**The frozen block is not computable with this port.** The strategy leg only produces a curve on
part of the window; elsewhere it returns an **empty run** — 0 orders, equity flat to the cent,
`Total Fees` at 0.00 USD — without raising any error. Measured 2026-10-08 (project `37468246`,
`list_backtests` plateau):

| Window | Length | Orders | Status |
|---|---|---|---|
| 2015-08-10 → 2015-10-10 | 2 months | **848** | trades |
| 2020-02-19 → 2020-03-23 | 1 month | 0 | **empty** |
| **2020-08-17 → 2022-08-16** | 24 months | **839** | trades |
| 2021-01-01 → 2022-01-01 | 12 months | 0 | **empty** |
| 2021-08-17 → 2022-08-16 | 12 months | 0 | **empty** |
| 2022-08-16 → 2023-08-16 | 12 months | 0 | **empty** |
| 2020-08-17 → 2026-09-30 (frozen block) | 6.1 years | — | **does not complete** (stalls, then aborted) |
| 2020-08-17 → 2026-09-30 (`mode: xle_hold`) | 6.1 years | 1 | completes |

Three explanations were tested and **all three refuted by measurement**:

1. **"the window is too short for the Ichimoku warm-up"** — refuted: `fall2015` traded 848
   orders in **two months**, and the empty windows include a full year;
2. **"the fine-fundamental data ends around 2022-08"** — refuted: the 2021 window is **entirely
   contained** in the `2020-08-17 → 2022-08-16` one (839 orders, including 453 equity points in
   2021 alone, 364 distinct values);
3. **"the start month alignment"** (both trading windows start in August) — refuted by a
   dedicated probe: `2021-08-17 → 2022-08-16` starts in August, is **entirely contained** in the
   trading window, and returns 0 orders.

What is established: the wall sits on the strategy's `FineFundamentalUniverseSelectionModel`
path (the same project's `xle_hold` leg, same node, same bounds, completes without difficulty)
and **the universe empties silently** — a selection returning no symbol raises no error, so the
alpha has no symbol, hence no *insight*, hence no order, and LEAN concludes normally. The exact
cause of the emptying **is not identified**; it is opened as a follow-up issue rather than
guessed at here.

A practical corollary, measured: **run duration betrays the emptying.** An empty 12-month window
completes in ~90 s where two months that trade take 6-8 min — universe selection dominates the
cost, and an empty universe costs nothing. `progress` is a pure temporal ratio and says nothing;
the only discriminating read is the **equity curve** (flat to the cent = empty run).

## BEATS / NO BEATS verdict

**On the computable part of the frozen block, the pre-registered test returns `INCONCLUSIVE`.**

The frozen block running from 2020-08-17 to 2026-09-30 not being computable (previous section),
the verdict bears on **2020-08-17 → 2022-08-16** — the first 24 months of the block, **entirely
contained** in it, and the longest window on which the strategy leg actually produces a curve.
The test is the pre-registered one, unchanged: block bootstrap, **block = 21 sessions, 10,000
resamples, seed 42**, paired session by session, placebo at 21 sessions.

| | Sharpe (instrument) | Cumulative | Max drawdown |
|---|---|---|---|
| Strategy | 0.6078 | +2.140 % | -2.619 % |
| XLE baseline (`xle_hold`) | 1.333 | +127.442 % | -25.983 % |

| Test | Sharpe difference | p (beats) | p (underperforms) | Verdict |
|---|---|---|---|---|
| Main (520 common sessions) | -0.7252 | 0.8059 | **0.1941** | **`INCONCLUSIVE`** |
| Placebo (baseline shifted 21 sessions) | -1.2382 | 0.9134 | 0.0866 | `INCONCLUSIVE` |

**What the verdict says, exactly.** The strategy **does not beat** XLE buy-and-hold — the Sharpe
difference is negative and the strategy's cumulative (+2.140 %) is very far from the baseline's
(+127.442 %). But the frozen threshold requires p < 0.05 to conclude either `BEATS` **or**
`UNDERPERFORMS`: at p = 0.1941 one **cannot** conclude significant underperformance on this
sample either. The verdict is therefore `INCONCLUSIVE`, and that is the verdict, not a fallback.

**The placebo fabricates no effect**: shifting the baseline 21 sessions into the future leaves
the Sharpe difference negative (-1.2382) and the underperformance p **drops** (0.0866) instead of
fabricating a `BEATS` — the test is not a one-way device.

**Honest limitation, frozen before the first calculation.** A verdict on a single window remains
a verdict on a single window. Here the limitation is tighter than planned: the verdict bears on
24 months instead of the frozen block's 74, because the port cannot produce the strategy leg
beyond. That reduction is a **harness constraint**, not an analysis choice, and it is measured
(window table above). The result remains out-of-sample — 2020-08-17 → 2022-08-16 was used for no
tuning, the port having been written and debugged on 2015-01-01 → 2020-08-16.

**What this verdict does not say.** It says nothing about the 2015-01-01 → 2020-08-16 window
(strategy leg not executed under the current code), nor about the `2020 Recovery` and
`2020 Crash` windows (one not executed, the other empty). The level gap with the values published
by the article (`fall2015`: -2.504 vs -0.31) is not explained by this verdict and remains open:
the article publishes neither capital nor fee model, and the port runs under real brokerage fees.

## Reference

Gurrib, I., Kamalov, F., & Elshareif, E. (2021). *Can the leading US energy stock prices be
predicted using the Ichimoku cloud?* International Journal of Energy Economics and Policy,
11(1), 41–51. https://doi.org/10.32479/ijeep.10260 (SSRN version 2020, abstract 3520582).
PDF archived in the shared bibliography under `Trading/`.

The reference study uses a **fixed selection built on end-of-period weights** (look-ahead
bias documented by the QC article itself); the port keeps the QC article's **monthly**
fine-fundamental universe, which removes that bias — absolute Sharpe levels are therefore
not directly comparable to Gurrib et al.; the **strategy-vs-XLE confrontation under the
same harness** is what counts.
