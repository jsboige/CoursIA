# QuantConnect Shared Library - Documentation

> **Bibliothèque utilitaire partagée** pour notebooks QuantConnect
> `QuantConnect/shared/` - Modules Python réutilisables

---

## Vue d'Ensemble

La **shared library** est une collection de modules Python utilitaires utilisés dans tous les notebooks QuantConnect pour :
- Feature engineering ML
- Configuration backtests
- Entraînement modèles ML
- Visualisations
- Indicateurs personnalisés

**Emplacement** : `MyIA.AI.Notebooks/QuantConnect/shared/`

---

## Modules Disponibles

### 1. `features.py` - Feature Engineering

**Fonctions principales** :

```python
from shared.features import calculate_returns, add_technical_features

# Retours multi-périodes
returns_df = calculate_returns(prices, periods=[1, 5, 20])

# Features techniques (SMA, RSI, MACD, Bollinger)
features_df = add_technical_features(df, indicators={
    'sma': [20, 50],
    'rsi': 14,
    'macd': (12, 26, 9)
})
```

**Fonctions** :
- `calculate_returns(prices, periods)` : Calcule retours 1d, 5d, 20d, etc.
- `add_technical_features(df, indicators)` : Ajoute SMA, EMA, RSI, MACD, BB
- `create_labels(returns, method)` : Crée labels ML (binary/ternary/regression)
- `walk_forward_split(df, train_size, n_splits)` : Split temporel walk-forward
- `add_lagged_features(df, columns, lags)` : Features laggées (t-1, t-2, etc.)
- `feature_importance_scores(model, feature_names)` : Extraction importance

**Utilisé dans** : Notebooks 18-21 (ML Features Engineering)

---

### 2. `backtest_helpers.py` - Configuration & Métriques

**Fonctions principales** :

```python
from shared.backtest_helpers import (
    default_backtest_config,
    calculate_metrics,
    format_backtest_summary
)

# Configuration backtest standard
config = default_backtest_config(
    start='2020-01-01',
    end='2023-12-31',
    initial_capital=100000
)

# Métriques performance
metrics = calculate_metrics(equity_curve, benchmark=spy_series)

# Résumé formaté
print(format_backtest_summary(metrics, 'My Strategy'))
```

**Fonctions** :
- `default_backtest_config()` : Config backtest par défaut
- `calculate_metrics(equity, benchmark)` : Sharpe, Sortino, max DD, alpha/beta
- `format_backtest_summary(metrics)` : Texte formaté pour rapport
- `compare_strategies(strategies)` : Comparaison multi-stratégies
- `annualized_sharpe(returns)` : Sharpe ratio annualisé
- `is_trading_day(date)` : Vérifie jour de trading

**Métriques calculées** :
- Total Return, Annualized Return, Volatility
- Sharpe Ratio, Sortino Ratio, Calmar Ratio
- Max Drawdown, Win Rate
- Alpha, Beta (si benchmark fourni)

**Utilisé dans** : TOUS les notebooks de backtest

---

### 3. `ml_utils.py` - Machine Learning Utilities

**Fonctions principales** :

```python
from shared.ml_utils import train_classifier, evaluate_model, save_to_objectstore

# Entraînement
model = train_classifier(X_train, y_train, model_type='random_forest')

# Évaluation
metrics = evaluate_model(model, X_test, y_test, task='classification')

# Persistance (QuantConnect ObjectStore ou local)
save_to_objectstore(model, 'my_model', qc_algorithm=self, local_path='models/')

# Chargement
loaded_model = load_from_objectstore('my_model', local_path='models/')
```

**Fonctions** :
- `train_classifier(X, y, model_type)` : Random Forest, XGBoost, LightGBM, Logistic
- `train_regressor(X, y, model_type)` : Random Forest, XGBoost, SVR, Linear
- `evaluate_model(model, X, y, task)` : Accuracy, precision, recall, F1, MAE, RMSE, R²
- `save_to_objectstore(model, name)` : Sauvegarde QC ObjectStore ou local
- `load_from_objectstore(name)` : Chargement modèle
- `cross_validate_walk_forward()` : Validation walk-forward time series

**Utilisé dans** : Notebooks 19-25 (ML/DL/AI)

---

### 4. `plotting.py` - Visualisations

**Fonctions principales** :

```python
from shared.plotting import (
    plot_backtest_results,
    plot_feature_importance,
    plot_cumulative_returns
)

# Résultats backtest
plot_backtest_results(results_df, benchmark=spy_series)

# Feature importance (modèles tree-based)
plot_feature_importance(model, feature_names, top_n=20)

# Retours cumulatifs
plot_cumulative_returns(strategy_returns, benchmark_returns)
```

**Fonctions** :
- `plot_backtest_results(results, benchmark)` : Equity curve, drawdown, returns distribution
- `plot_feature_importance(model, feature_names)` : Barplot importance
- `plot_confusion_matrix(y_true, y_pred)` : Heatmap classification
- `plot_returns_distribution(returns)` : Histogram + Q-Q plot
- `plot_correlation_matrix(df)` : Heatmap corrélations
- `plot_cumulative_returns(strategy, benchmark)` : Courbe cumulée

**Utilisé dans** : TOUS les notebooks avec visualisations

---

### 5. `indicators.py` - Indicateurs Personnalisés

**Classes principales** :

```python
from shared.indicators import (
    CustomMomentumIndicator,
    TrendStrengthIndicator,
    VolatilityBandIndicator
)

# Momentum
momentum = CustomMomentumIndicator('momentum', period=20)
momentum.Update(time, price)
if momentum.IsReady:
    value = float(momentum.Current)

# Force de tendance
trend = TrendStrengthIndicator('trend', period=14)
trend.Update(time, high, low, close)

# Bandes volatilité
vol_band = VolatilityBandIndicator('vol_band', period=20, multiplier=2.0)
vol_band.Update(time, high, low, close)
upper, middle, lower = vol_band.UpperBand, vol_band.MiddleBand, vol_band.LowerBand
```

**Classes** :
- `CustomMomentumIndicator` : Momentum sur période
- `TrendStrengthIndicator` : Force de tendance (ADX simplifié)
- `VolatilityBandIndicator` : Bandes volatilité ATR-based
- `IndicatorValue` : Wrapper valeur + timestamp

**Utilisé dans** : Notebooks 11, 18 (Technical Indicators)

---

## Import Global

```python
# Import tous les modules
from shared import features, indicators, ml_utils, plotting, backtest_helpers

# Import fonctions spécifiques
from shared.features import calculate_returns, add_technical_features
from shared.backtest_helpers import default_backtest_config, calculate_metrics
from shared.ml_utils import train_classifier, save_to_objectstore
from shared.plotting import plot_backtest_results, plot_feature_importance
from shared.indicators import CustomMomentumIndicator
```

---

## Workflow Type - Backtest Complet

```python
import pandas as pd
from shared import backtest_helpers, features, plotting

# 1. Configuration
config = backtest_helpers.default_backtest_config(
    start='2020-01-01',
    end='2023-12-31',
    initial_capital=100000
)

# 2. Feature engineering
df = features.add_technical_features(prices_df, indicators={'sma': [20, 50]})
returns_df = features.calculate_returns(prices, periods=[1, 5, 20])

# 3. Backtest (votre code ici)
# ...

# 4. Métriques
metrics = backtest_helpers.calculate_metrics(equity_curve, benchmark)

# 5. Visualisation
plotting.plot_backtest_results(results_df, benchmark)

# 6. Rapport
print(backtest_helpers.format_backtest_summary(metrics))
```

---

## Workflow Type - ML Trading Model

```python
import numpy as np
from shared import features, ml_utils, plotting

# 1. Features
X = features.add_technical_features(df, indicators={'sma': [20], 'rsi': 14})
y = features.create_labels(forward_returns, method='binary')

# 2. Split temporel
splits = features.walk_forward_split(df, train_size=0.7, n_splits=5)
train_df, test_df = splits[0]

# 3. Entraînement
model = ml_utils.train_classifier(
    X_train, y_train,
    model_type='random_forest',
    n_estimators=100
)

# 4. Évaluation
metrics = ml_utils.evaluate_model(model, X_test, y_test, task='classification')

# 5. Persistance
ml_utils.save_to_objectstore(model, 'rf_classifier', local_path='models/')

# 6. Feature importance
plotting.plot_feature_importance(model, feature_names, top_n=15)
```

---

## Bonnes Pratiques

1. **Toujours utiliser `default_backtest_config()`** pour configuration consistante
2. **Normaliser les features** avant ML (`StandardScaler` ou similaire)
3. **Walk-forward validation** pour time series (pas random K-fold)
4. **Sauvegarder les modèles** avec `save_to_objectstore()` pour reproductibilité
5. **Comparer au benchmark** (SPY) dans tous les backtests
6. **Utiliser `calculate_metrics()`** pour métriques standardisées

---

## Dépendances

```txt
pandas
numpy
matplotlib
seaborn
scikit-learn
scipy
```

Optionnels (ML avancé) :
```txt
xgboost
lightgbm
```

---

## Version

**Version** : 1.0.0
**Auteur** : CoursIA - QuantConnect AI Trading Series
**Dernière MAJ** : 2026-03-22
