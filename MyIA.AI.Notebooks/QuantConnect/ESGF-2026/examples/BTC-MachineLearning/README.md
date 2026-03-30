# BTC Machine Learning (ID: 21047688)

Prediction de direction BTC avec ML (RandomForest, SVC, XGBoost).

## Architecture

- `main.py` - Algorithme enhanced (9 features: SMA, RSI, EMA x4, ADX, ATR)
- `main-simple.py` - Version simple (3 features: SMA20, RSI, DailyReturn)
- `research.ipynb` - Training enhanced (ta, sklearn, xgboost)
- `research-simple.ipynb` - Training simple (RF seulement)
- `IMPROVEMENTS.md` - Documentation des ameliorations (2026-02-15)

## Ameliorations recentes (2026-02-15)

### 1. Fix data leakage

- Training set fixe: 2021-2022 (2 ans pre-backtest)
- Backtest period: 2023-2024 (1.5 ans out-of-sample)
- Elimination complete du data leakage

### 2. Risk management

- Stop-loss: -5%
- Take-profit: +10%
- Tracking prix d'entree

### 3. Retraining periodique

- Tous les 30 jours
- Lookback: 365 derniers jours
- Adaptation au regime de marche

### 4. Position sizing probabiliste

- `predict_proba()` au lieu de `predict()`
- Confidence threshold LONG: > 0.6
- Confidence threshold EXIT: < 0.4
- Zone d'incertitude: 0.4-0.6 (pas de trade)
- Position proportionnelle a la confiance

## Concepts enseignes

- Feature engineering (indicateurs techniques -> features ML)
- Object Store pour persistance modele
- Train/test split temporel strict (eviter data leakage)
- Comparaison modeles (RF vs SVC vs XGBoost)
- Risk management (stop-loss, take-profit)
- Retraining adaptatif
- Position sizing probabiliste (Kelly-like)

## Status compilation

- **CompileId**: `e28e4aa0f7a3267c8968e150e47b0bc7-4275d99ab3c0557cc41c0e69c281de70`
- **State**: BuildSuccess
- **Lean Version**: 2.5.0.0.17533
- **Date**: 2026-02-15

## Prochaines etapes

1. Lancer backtest via UI (2023-2024)
2. Analyser resultats vs 8 backtests precedents (0 trades)
3. Ajuster thresholds si necessaire
