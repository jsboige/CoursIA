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
that does not trade neither confirms nor refutes the article. See the "Out-of-sample extension"
section below: the same signature has since been reproduced on four other windows **pre-fix**,
which rules out the initial explanation ("23 sessions, too short to arm the universe") — the
actual cause (missing base-constructor chaining) and its fix are documented there.

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

**Port defect found then fixed (#19863): the fine universe was never armed.** Pre-fix runs
(measured 2026-10-08, project `37468246`) showed **empty** windows — 0 orders, equity flat to the
cent, no error — alongside windows that traded:

| Window | Length | Orders | Status (pre-fix) |
|---|---|---|---|
| 2015-08-10 → 2015-10-10 | 2 months | **848** | trades |
| 2020-02-19 → 2020-03-23 | 1 month | 0 | **empty** |
| **2020-08-17 → 2022-08-16** | 24 months | **839** | trades |
| 2021-01-01 → 2022-01-01 | 12 months | 0 | **empty** |
| 2021-08-17 → 2022-08-16 | 12 months | 0 | **empty** |
| 2022-08-16 → 2023-08-16 | 12 months | 0 | **empty** |
| **2020-08-17 → 2026-09-30 (frozen block, fixed)** | 6.1 years | **4,860** | completes and trades |

Three explanations were first tested and **refuted by measurement** (window too short / fine-data
end / start-month alignment). An instrumented probe (issue #19863) then reading LEAN's public
source named the exact cause: `EnergyTopTenUniverseSelectionModel` subclassed
`FineFundamentalUniverseSelectionModel` **without chaining any base constructor** — the canonical
QC pattern requires `super().__init__(self.select_coarse, self.select_fine)`. Without it the fine
universe is **never constructed**: the probe's `fine_calls` counter is **0 on every pre-fix run**
(including the trading ones), the universe degenerates to the raw coarse (~5,000 symbols with
fundamental data), the monthly lock (`self.month`, set inside `select_fine`) never arms — daily
re-selection of ~5,000 symbols, >1M *insights* — and equal weighting across ~5,000 symbols
(~$200 per position) rounds most order sizes to 0 shares: that is the origin of the "empty"
windows. A selection producing no order is not an error for LEAN; the run concludes normally.

**Fix** (commit `a745f2545d`, one line): canonical base-constructor chaining. The corrected
container run **completes and trades: 1,692 orders** over 2020-08-17 → 2022-08-16 (harness Sharpe
0.049, net -2.312 %, MaxDD 30.5 %). And at the scale of the whole frozen block: the corrected
full-block run (`22fde01f1ad65`, 2020-08-17 → 2026-09-30) **completes and trades: 4,860 orders** —
net +12.6 %, CAGR 1.96 %, harness Sharpe -0.041, against +310.5 % / 25.93 %/yr for the XLE
baseline of the same block (measured 2026-10-08, recorded in [#19867](https://github.com/jsboige/CoursIA/pull/19867)).
The 2021+ windows, re-run with the corrected probe, are tracked on #19863.

A practical corollary, measured: **run duration betrays the emptying.** An empty 12-month window
completes in ~90 s where two months that trade take 6-8 min — universe selection dominates the
cost, and an empty universe costs nothing. `progress` is a pure temporal ratio and says nothing;
the only discriminating read is the **equity curve** (flat to the cent = empty run).

## BEATS / NO BEATS verdict

**On the corrected container window (24 months, the only one where the pre-registered bootstrap
has been replayed), the test returns `INCONCLUSIVE` — computed on the corrected port.**

The verdict bears on **2020-08-17 → 2022-08-16**, the corrected container-run window (1,692
orders, fine universe armed). The test is the pre-registered one, unchanged: block bootstrap,
**block = 21 sessions, 10,000 resamples, seed 42**, paired session by session, placebo at 21
sessions.

| | Sharpe (instrument) | Cumulative | Max drawdown |
|---|---|---|---|
| Strategy (fixed, `4cdcd965`) | 0.0788 | -2.513 % | -30.517 % |
| XLE baseline (`xle_hold`) | 1.303 | +123.020 % | -25.983 % |

| Test | Sharpe difference | p (beats) | p (underperforms) | Verdict |
|---|---|---|---|---|
| Main (521 common sessions) | -1.2242 | 0.9132 | **0.0868** | **`INCONCLUSIVE`** |
| Placebo (baseline shifted 21 sessions) | -1.517 | 0.9241 | 0.0759 | `INCONCLUSIVE` |

**What the verdict says, exactly.** The strategy **does not beat** XLE buy-and-hold — the Sharpe
difference is negative and the strategy's cumulative (-2.513 %) is very far from the baseline's
(+123.020 % — the 2021-2022 energy rally). But the frozen threshold requires p < 0.05 to conclude
either `BEATS` **or** `UNDERPERFORMS`: at p = 0.0868 one **cannot** conclude significant
underperformance on this sample either. The verdict is therefore `INCONCLUSIVE`, and that is the
verdict, not a fallback. The first version of this verdict (difference -0.7252, p 0.1941),
computed before the universe fix, measured the degenerate raw coarse — it is **superseded** by
this one; both are kept in the #19678 thread for traceability.

**The placebo fabricates no effect**: shifting the baseline 21 sessions into the future leaves
the Sharpe difference negative (-1.517) and the verdict `INCONCLUSIVE` — the test is not a
one-way device.

**Honest limitation, frozen before the first calculation.** A verdict on a single window remains
a verdict on a single window. The corrected port **does** produce the strategy leg over the whole
block (4,860 orders, run `22fde01f1ad65`); what remains bounded to 24 months is the
**pre-registered statistical test**: its block bootstrap has only been replayed on the
2020-08-17 → 2022-08-16 container (1,692 orders) — until it is replayed on the full block,
significance is measured on those 24 months only, the full block having only undergone the raw
comparison (net +12.6 % vs +310.5 % — readable `NO BEATS`, no measured significance). The result
remains out-of-sample — 2020-08-17 → 2022-08-16 was used for no tuning, the port having been
written and debugged on 2015-01-01 → 2020-08-16.

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
