# ML-FinBERT-Sentiment (HandsOn Ex19)

**Asset class:** US Equities (most volatile of the 10 most liquid)
**Cloud project ID:** 29936073 (HandsOn-Ex19-FinBERT-Sentiment)

## Description

Faithful port of the book's Example 19 base model (*Hands-On AI Trading*, chapter 06): FinBERT (`ProsusAI/finbert`) scores the last 10 days of Tiingo articles, the exponentially weighted aggregate drives 100% long or 25% short, monthly.

**The model runs inside the algorithm on QC Cloud** (PyTorch variant, `local_files_only=True` as in the book) — measured by probes `probe2-bitmask-finbert` and `probe3-tiingo-decode` on 2026-10-05: `torch`, `transformers` and even `tensorflow` import on the nodes, and inference returns its probabilities there.

## History of the "0 trades" (closed 2026-10-05)

The v1/v2 portages called `add_data(TiingoNews, "AAPL")` with a **string ticker**. TiingoNews requires an already-mapped equity `Symbol` — the call raises `The custom data type TiingoNews requires mapping, but the provided ticker is not in the cache`, swallowed by the `try/except` → zero articles → zero trades. The book passes `security.symbol` (from the universe); the port now does the same. The old "TF unavailable on QC Cloud" diagnosis was wrong on both counts.

**Second layer (closed the same day)**: the faithful port crashed with `FATAL UNHANDLED EXCEPTION` ~13 s after `initialize` (reproduced twice). Cause: the book creates the SPY Symbol **without subscribing it** (a mere calendar reference for `date_rules.month_start`) — on current QC nodes, a `date_rules` targeting an unsubscribed symbol kills the algorithm. Fix: `self.add_equity("SPY", Resolution.DAILY)` (documented divergence #2 in `main.py`). Isolated by cascading probes: probe4 (8/8 initialize steps) and probe5 (full January pipeline, mask 255/255) passed — their only difference: the SPY subscription.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-FinBERT-Sentiment"` (the model must be in the local HuggingFace cache).
**QC Cloud:** project 29936073, `create_compile` → `create_backtest`.

## Backtest Metrics

| Metric | Value (2022, book period) |
|--------|---------------------------|
| Sharpe | __SHARPE__ |
| Total return | __NETPROFIT__ |
| Max drawdown | __DD__ |
| Orders | __ORDERS__ |
| Book reference (tearsheet 6.60/6.61, OCR) | +123% cumulative over 2022 |

## Files

- `main.py` — Strategy: PyTorch port of the book's `FinbertBaseModelAlgorithm`
- `research.ipynb` — Sentiment model evaluation

## References

- *Hands-On AI Trading*, Section 06, Example 19 (01 Base Model)
- Book repo: `QuantConnect/HandsOnAITradingBook`, `06 Applied Machine Learning/19 FinBERT Model`
