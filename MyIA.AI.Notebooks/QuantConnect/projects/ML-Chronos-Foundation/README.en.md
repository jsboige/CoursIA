# ML-Chronos-Foundation (HandsOn Ex18)

**Asset class:** US Equities (top 10)
**Cloud project ID:** None (local only)

## Description

Amazon Chronos T5 foundation model for time series forecasting. Biweekly rebalance based on forecast direction.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-Chronos-Foundation"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.277 |
| CAGR | 7.23% |
| Max Drawdown | 13.5% |
| Model | Chronos T5 (Amazon) |
| Rebalance | Biweekly |

## Fine-Tuned Variant (Example 18/02)

`main_finetuned.py` is a faithful port of the book (`06 Applied Machine Learning/18
Amazon Chronos Model/02 Fine-Tuned Model/main.py`, `HandsOnAITradingBook` repository at
commit `e025f21`): retraining runs **inside the algorithm**, at the first quarterly
rebalance, then `ChronosPipeline.predict` supplies the forecast curves and SciPy the
max-Sharpe weights. It is **not CI-runnable** (GPU, `chronos` and `gluonts` required) and
is not deployed to QC Cloud.

Retraining is therefore also carried **outside** the algorithm, by a harness (`finetune/`)
that makes it measurable on a local GPU:

- `finetune/run_finetune_chronos.py` — retrains per seed, then compares the base and the
  retrained model out of sample;
- `finetune/chronos_training.py` — the `chronos` training module, **vendored** from tag
  `v2.3.2` (Apache-2.0). The book imports `chronos.scripts.training.train`, a module
  **absent from the PyPI wheel** (the file lives at the upstream repository root): the
  vendored copy carries its provenance header, and `main_finetuned.py` falls back to it
  when the upstream import fails.

### Protocol

- **Universe**: `AAPL, MSFT, NVDA, AMZN, GOOGL` — a fixed basket of five mega-caps.
- **Training**: 2016-01-01 → 2021-12-31. **Out of sample**: 19 quarterly origins
  2022-01-03 → 2026-07-01 (first trading day of each quarter from 2022-01-01), each
  evaluated on its 63-day forecast horizon — the last evaluated horizon runs into
  early September 2026.
- Book recipe: `context_length` 126 days, `prediction_length` 63 days, `learning_rate`
  1e-5, `adamw_torch_fused`, batch 32, accumulation 2, `tf32` (Ampere), 20 forecast
  samples per origin.
- **Error**: MAE, MASE (step-1 naive over the actual window) and WQL (quantiles
  0.1 / 0.25 / 0.5 / 0.75 / 0.9), averaged over the five series, per quarterly origin
  (19 origins).
- **Significance**: Diebold-Mariano test paired by origin on the MAE loss. Quarterly
  origins do not overlap: no Newey-West correction. The p-value is the normal
  approximation one, liberal at 19 origins — the Harvey, Leybourne and Newbold correction
  would only widen it.
- **Strategy effect**: the book's SLSQP weights (long-only, sum 1, maximising the Sharpe
  of the forecast curves), quarterly rebalance, **5 basis points** of cost on turnover.
  Both arms play **the same** origin, with the same draw seed.
- **Seeds**: 1, 2, 3 and 42.

### Deviations from the book, assumed

| Deviation | Reason |
|---|---|
| `max_steps` = 300 (the book: 3) | 3 steps retrain nothing; 3 is a cloud runtime budget, not a method choice |
| `torch_compile` = `False` | the book compiles for Linux/Ampere; `torch.compile` is not portable on this workstation |
| One retraining per seed over 2016-2021, evaluated out of sample | the book retrains every quarter; the harness isolates the retraining effect on a fixed window, which makes the two arms comparable |
| Fixed five mega-cap universe | the book selects the five most liquid tickers by dollar volume, unavailable outside QC. **This universe is Mag7**: no gain claim is made here (see the verdict) |
| `yfinance` data (adjusted closes) | the book reads LEAN engine history; the harness runs outside QC |

### Out-of-sample result

| Seed | MAE base | MAE retrained | MASE base | MASE retrained | DM (statistic) | DM (p) | Sharpe base | Sharpe retrained |
|---|---|---|---|---|---|---|---|---|
| 1 | 18.40 | 17.61 | 6.24 | 5.99 | 0.83 | 0.409 | 0.746 | 0.603 |
| 2 | 17.78 | 16.87 | 6.03 | 5.69 | 1.43 | 0.153 | 0.664 | 0.751 |
| 3 | 19.21 | 17.82 | 6.50 | 6.02 | 1.68 | 0.093 | 0.588 | 0.746 |
| 42 | 18.31 | 17.30 | 6.27 | 5.83 | 1.14 | 0.256 | 0.559 | 0.675 |
| **mean** | **18.43** | **17.40** | **6.26** | **5.88** | — | — | **0.639** | **0.694** |

Mean WQL: 0.0745 → 0.0732. Mean CAGR: 17.5% → 18.0%. Mean max drawdown:
−29.1% → −33.5%. The test's `mean_diff` field is signed `base − retrained`: a positive
value means the **base** model has the larger error.

**Precision — `NO BEATS`.** The retrained model is more accurate on **all four seeds**
(mean MAE 18.43 → 17.40, about −5.5%), but **no** seed reaches the 5% threshold (p from
0.093 to 0.409). The effect is therefore stable in sign and too small to be told apart
from noise at this sample size (19 origins × 5 series).

**Strategy — unstable effect, no gain claimed.** Mean Sharpe rises (0.639 → 0.694) and so
does CAGR, but the sign **changes with the seed** (one seed in four sees the retrained
model fall back) and the worst drawdown deepens on average.

**What these numbers are not.** They do not compare to the 0.277 Sharpe published for
example 18/01: that one comes from a LEAN backtest over 2015-2026, whereas the
measurement above comes from a harness outside QC, over another window and another
universe.

**The disagreement between the two error measurements is worth stating.** The training
loss does fall over the steps (mean 4.83 over the 300 steps of the last seed, 4.66 at the
last step), without carrying over out of sample. That is the expected behaviour of a fit
to the training window, for a model of this size (`chronos-t5-tiny`) and 300 steps.

### Reproducing the measurement

```bash
# local GPU; the measurement does not need QC Cloud
python finetune/run_finetune_chronos.py --stage all --seeds 1 2 3 42 \
    --max-steps 300 --run-dir <output-directory>
```

The harness writes one file per seed into `<output-directory>/results/`, plus a
`summary.json` aggregating the seeds. The committed copies live under
`finetune/measures/`: the QuantConnect tree ignores `results/`, and `measures/` is the
repository convention for measurements kept in git.

## Files

- main.py - Strategy (v1.0, Chronos forecasting)
- main_finetuned.py - Fine-tuned variant (example 18/02, not CI-runnable)
- finetune/ - Out-of-sample measurement harness (local, outside QC Cloud)

## References

- Hands-On AI Trading, Section 06, Example 18
