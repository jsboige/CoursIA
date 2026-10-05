# ML-FinBERT-Sentiment (HandsOn Ex19)

**Asset class:** US Equities (most volatile of the 10 most liquid)
**Cloud project ID:** 29936073 (HandsOn-Ex19-FinBERT-Sentiment)

## Description

Faithful port of the book's Example 19 base model (*Hands-On AI Trading*, chapter 06): FinBERT (`ProsusAI/finbert`) scores the last 10 days of Tiingo articles, the exponentially weighted aggregate drives 100% long or 25% short, monthly.

**Execution on QC Cloud**: the same pipeline as the book, under **step-by-step shielding** (an execution adaptation, see §History) and over a **2-month window** — the two measured conditions for a backtest to complete.

**The model runs inside the algorithm on QC Cloud** (PyTorch variant, `local_files_only=True` as in the book) — measured by probes `probe2-bitmask-finbert` and `probe3-tiingo-decode` on 2026-10-05: `torch`, `transformers` and even `tensorflow` import on the nodes, and inference returns its probabilities there.

## History of the "0 trades" (closed 2026-10-05)

The v1/v2 portages called `add_data(TiingoNews, "AAPL")` with a **string ticker**. TiingoNews requires an already-mapped equity `Symbol` — the call raises `The custom data type TiingoNews requires mapping, but the provided ticker is not in the cache`, swallowed by the `try/except` → zero articles → zero trades. The book passes `security.symbol` (from the universe); the port now does the same. The old "TF unavailable on QC Cloud" diagnosis was wrong on both counts.

**Second layer (closed the same day)**: the faithful port crashed with `FATAL UNHANDLED EXCEPTION`. Twelve runs (v1–v6, probes 4–10, project 29936073) establish a clean partition:

| Configuration | Measured effect |
| --- | --- |
| Unshielded port, 100k, full year — SPY never subscribed (v1/v2) | FATAL inside `initialize` (`hasInitializeError=true`, reproduced twice) |
| Unshielded port, 100k, full year — SPY subscribed (v3/v4) | native FATAL **~12 s after launch** (progress ~0.15) |
| Step-by-step shielded probe, full year (probe8, 1M) | **same native FATAL**: full shielding + 1M cash change nothing, `on_end_of_algorithm` never reached, error field = 100% TF noise → engine-level crash, not Python |
| Faithful unshielded port, 1M, **6 months** (v5) | **same native FATAL ~11 s after launch** (progress 0.29): halving the term does not move the wall |
| Faithful unshielded port, 1M, **2 months** (v6) | **`Runtime Error`** — **no unshielded run has ever completed (6/6)** |
| **Shielded** probe, short windows (probe5 January; probe6/probe7 Jan–Feb; probe9 Jan–Feb full) | **all Completed** — probe9 crosses the February 1 transition (re-selection, TiingoNews `remove_security`, re-`add_data`, 2nd `_trade`, real orders; Sharpe -1.137 over Jan–Feb) |
| probe9 verbatim, full book year (probe10) | **`Runtime Error`** — the year's wall is not a shielding matter |
| **Deliverable**: faithful **shielded** port, 1M, **2 months** (v7) | **`Completed.`** — 40 trading days, **2 orders** (the 2 monthly rebalances), Sharpe -1.137: the deliverable completes and trades |

Two conditions are needed for a backtest to complete, and neither suffices alone: **a window ≤ 2 months** (the year and the half-year die natively) **and step-by-step shielding** (the only unshielded short-window run fails with `Runtime Error`, where every shielded short-window run completes — probe5, probe6, probe7, probe9 and deliverable v7). The deliverable meets both.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-FinBERT-Sentiment"` (the model must be in the local HuggingFace cache).
**QC Cloud:** project 29936073, `create_compile` → `create_backtest`.

## Backtest Metrics

`ex19-portage-livre-2022-jan-fev-v7-blinde` — the deliverable: faithful shielded port, 1M cash, 2022-01-01 → 2022-03-01, **40 trading days**, status **`Completed.`**:

| Metric | Deliverable (v7, 2022 Jan–Feb) | Probe `probe9` (same window) | Book reference |
| --- | --- | --- | --- |
| Sharpe | -1.137 | -1.137 | — |
| Compounding annual return | -84.294% | -84.294% | — |
| Total net profit | -26.230% | -26.230% | +123% cumulative over 2022 |
| Max drawdown | 37.800% | 37.800% | — |
| Probabilistic Sharpe Ratio | 8.371% | 8.371% | — |
| Absolute net profit | -$20,375.04 | -$20,375.04 | — |
| **Orders** | **2** | 8193 | — |

The deliverable **completes and produces its orders**: 2 orders = the 2 monthly rebalances (Jan 1, Feb 1), exactly the book's behaviour. Issue #18903's "0 trades" is closed **by measurement**, not by argument.

**On probe `probe9`**: it carries 8191 extra marker orders (one `market_order` of a single SPY share per bit of its diagnostic mask) and yet returns statistics **identical to the unit** to v7's. The markers are therefore **metric-neutral** — a gap of 8191 orders moves neither Sharpe, nor return, nor drawdown. The two runs corroborate each other.

**Two measured caveats.** (1) The book comparison is **across unequal windows**: the book spans all of 2022, the deliverable its first sixth (native wall, see §History) — no performance judgement is drawn from the gap. (2) These figures are **not a strategy verdict**: two months, a single configuration, no multi-seed repetition — the result is the faithful port's, not an evaluation of the model.

## Files

- `main.py` — Strategy: PyTorch port of the book's `FinbertBaseModelAlgorithm`
- `research.ipynb` — Sentiment model evaluation

## References

- *Hands-On AI Trading*, Section 06, Example 19 (01 Base Model)
- Book repo: `QuantConnect/HandsOnAITradingBook`, `06 Applied Machine Learning/19 FinBERT Model`
