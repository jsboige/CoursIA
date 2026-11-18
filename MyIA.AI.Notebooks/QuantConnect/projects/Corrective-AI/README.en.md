# Corrective AI — EUR/USD intraday seasonality + meta-labeling (Ch. 08-02)

**Hands-On AI Trading**, chapter 08-02 — faithful port of the "Application of Corrective Artificial Intelligence Applied" episode. Tracked by [#18901](https://github.com/jsboige/CoursIA/issues/18901). French README is the primary documentation.

## Mechanism (the book)

1. **Primary strategy** — EUR/USD intraday seasonality of Breedon and Ranaldo (2012): **sell during European business hours** (03:00–09:00 ET), **buy during US business hours** (11:00–15:00 ET), flat otherwise. Out of sample (Oct. 2021 – Jan. 2023, 1-minute EBS bars) the book measures a **0.88 Sharpe** for the primary alone.
2. **Corrective AI** — the book corrects the primary trade by trade with a gradient boosting model of more than one hundred predictors through the **paid** predictnow.ai API: announced Sharpe 1.29 (+0.41) over the same period.

## This port

The predictnow.ai API is paid and proprietary: this port implements the corrective **principle** without a paid dependency, via **meta-labeling** (López de Prado, *Advances in Financial Machine Learning*, 2018):

- the trade unit is one window (European or American) of the primary;
- at each entry, a walk-forward-trained classifier (gradient boosted trees, `sklearn`) predicts the probability that the window will be a winner;
- the window is taken only above the threshold (`sizing: filter`) — or sized by probability (`sizing: scale`);
- declared gap vs the book: **~16 ex-ante predictors** (minute returns/volatilities, window side, weekday, rolling primary win-rates, streak) against **>100** at predictnow.ai.

## Parameters (backtests without recompilation)

| Parameter | Default | Role |
|---|---|---|
| `start` / `end` | 2021-10-01 / 2023-01-31 | window (`YYYY-MM-DD`) |
| `use_meta` | `true` | `false` = primary-only leg |
| `threshold` | `0.5` | probability threshold (`filter`) |
| `seed` | `0` | classifier seed (multi-seed, rule §C) |
| `retrain_days` | `21` | walk-forward retraining cadence |
| `min_train` | `120` | minimum past windows before the first meta trade |
| `sizing` | `filter` | `filter` or `scale` |
| `swap_sides` | `false` | `true` = Breedon-Ranaldo paper convention (buy EU / sell US), the inverse convention tested empirically |

Declared choices: labels on gross entry→exit returns (minute mids; engine fees on actual fills only); no entry during the walk-forward warm-up (`min_train`) nor during the 5-day data warm-up; windows with no usable minute history (e.g. January 1st, market closed) are skipped.

## Results

See `research.ipynb` (book window: primary vs meta, multi-seed ≥ 4, Diebold-Mariano test, reported bias — `BEATS` / `NO BEATS` / `INCONCLUSIVE` verdict per rule §C) and the 2018-2026 long-window robustness table. Metrics come from the QC backtests cited in the delivery PR body.

## History

The exploratory v1 of this folder (SMA crossover on SPY/TLT/GLD + rule-based corrective filter, backtest Sharpe −0.151 on the same QC project 30800636, April 2026) was a planned-exercise stub that did **not** match the actual chapter content; it is superseded by this port. QC Cloud project `30800636` (Corrective-AI-Ch08) is reused.

## References

- Breedon, T. & Ranaldo, A. (2012), "Intraday Patterns in FX Returns and Order Flow" — EUR/USD intraday seasonality.
- López de Prado, M. (2018), *Advances in Financial Machine Learning* — meta-labeling, ch. 3.
- *Hands-On AI Trading* (Jared Broad), ch. 08-02.
