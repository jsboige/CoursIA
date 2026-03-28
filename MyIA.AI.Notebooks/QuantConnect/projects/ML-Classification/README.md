# ML-Classification

ML Classification strategy using a pre-trained model loaded from QuantConnect ObjectStore.

## Prerequisites

This strategy **requires a pre-trained model** stored in QC ObjectStore. It cannot run as a standalone backtest without the model artifact.

### Setup Steps

1. Open the QC Research environment
2. Run `research_classification.ipynb` to train the model
3. Save the model to ObjectStore using `qb.object_store.save_bytes()`
4. Then run this algorithm as a backtest

### ObjectStore Keys

- `classification_model` — Serialized sklearn classifier (joblib format)
- `classification_config` — Model configuration JSON (feature columns, thresholds)

## Strategy Logic

- Predicts market direction (up/down) at T+1 using a RandomForest classifier
- Goes long when predicted probability > 0.55
- Liquidates when predicted probability < 0.45
- Trades SPY daily

## PEP8 Compliance

All custom methods use `snake_case` naming per PEP8 conventions. QC Framework methods (`Initialize`, `OnData`, etc.) retain their PascalCase naming as required by the API.
