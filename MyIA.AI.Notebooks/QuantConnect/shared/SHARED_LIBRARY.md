# QuantConnect Shared Library - Documentation

**Version**: 1.0.0
**Auteur**: CoursIA - QuantConnect AI Trading Series
**Dernière mise à jour**: 2026-03-23

---

## Table des matières

1. [Introduction](#introduction)
2. [Installation et Configuration](#installation-et-configuration)
3. [Aperçu des Modules](#apercu-des-modules)
4. [Module: backtest_helpers](#module-backtest_helpers)
5. [Module: features](#module-features)
6. [Module: indicators](#module-indicators)
7. [Module: ml_utils](#module-ml_utils)
8. [Module: plotting](#module-plotting)
9. [Workflows Courants](#workflows-courants)
10. [Bonnes Pratiques](#bonnes-pratiques)

---

## Introduction

La librairie `shared/` est un ensemble de modules Python utilitaires créés pour simplifier le développement de stratégies de trading algorithmique sur QuantConnect. Elle fournit des fonctions standardisées pour :

- **Feature engineering** pour le Machine Learning
- **Backtesting** et analyse de performances
- **Indicateurs techniques** personnalisés
- **Entraînement et évaluation** de modèles ML
- **Visualisations** standardisées

### Pourquoi utiliser shared/ ?

| Avantage | Description |
|----------|-------------|
| **Productivité** | Fonctions pré-testées, moins de code boilerplate |
| **Cohérence** | Mêmes métriques et visualisations across tous les projets |
| **Qualité** | Code validé avec tests unitaires |
| **Pédagogie** | Exemples et documentation pour chaque fonction |
| **Extensibilité** | Facile d'ajouter vos propres fonctions |

---

## Installation et Configuration

### Dans QuantConnect Lab (Notebooks)

```python
# Ajouter le chemin au syspath (au début du notebook)
import sys
sys.path.insert(0, '/Content/MyIA.AI.Notebooks/QuantConnect')

# Importer les modules
from shared.features import calculate_returns, add_technical_features
from shared.ml_utils import train_classifier, save_to_objectstore
from shared.plotting import plot_backtest_results
```

### Dans un Algorithme QuantConnect

```python
# Dans main.py ou un module auxiliaire
from AlgorithmImports import *

# Importer depuis shared/ (doit être dans le même projet)
# Note: Copier les modules .py nécessaires dans le projet QC
```

### En Local (Jupyter)

```python
# Cloner le repo et ajouter le chemin
import sys
sys.path.insert(0, 'path/to/CoursIA/MyIA.AI.Notebooks/QuantConnect')

from shared import features, ml_utils, plotting
```

### Dépendances Requises

```bash
# Core
pip install pandas numpy matplotlib seaborn

# ML
pip install scikit-learn xgboost lightgbm

# QuantConnect (dans l'environnement QC)
# Déjà installé dans le Lab
```

---

## Aperçu des Modules

| Module | Fonction Principale | Fonctions Clés |
|--------|---------------------|----------------|
| **backtest_helpers** | Configuration et analyse de backtests | `default_backtest_config`, `calculate_metrics`, `compare_strategies` |
| **features** | Feature engineering pour ML | `calculate_returns`, `add_technical_features`, `create_labels`, `walk_forward_split` |
| **indicators** | Indicateurs techniques custom QC | `CustomMomentumIndicator`, `TrendStrengthIndicator`, `VolatilityBandIndicator` |
| **ml_utils** | Training et persistence ML | `train_classifier`, `train_regressor`, `evaluate_model`, `save_to_objectstore` |
| **plotting** | Visualisations standardisées | `plot_backtest_results`, `plot_feature_importance`, `plot_confusion_matrix` |

---

## Module: backtest_helpers

**Fichier**: `shared/backtest_helpers.py` (335 lignes)

### Description

Configuration et analyse de backtests pour stratégies de trading. Fournit des fonctions standardisées pour calculer les métriques de performance et comparer les stratégies.

### Fonctions

#### `default_backtest_config(start, end, initial_capital, resolution)`

Crée une configuration de backtest par défaut.

```python
from shared.backtest_helpers import default_backtest_config

config = default_backtest_config(
    start='2020-01-01',
    end='2023-12-31',
    initial_capital=100000,
    resolution='Daily'
)
# Returns: {
#     'start_date': '2020-01-01',
#     'end_date': '2023-12-31',
#     'initial_capital': 100000,
#     'resolution': 'Daily',
#     'benchmark': 'SPY'
# }
```

#### `calculate_metrics(equity, benchmark, risk_free_rate)`

Calcule les métriques de performance d'un backtest.

```python
from shared.backtest_helpers import calculate_metrics
import pandas as pd

# Série de prix du portefeuille
equity = pd.Series([...], index=pd.date_range('2020-01-01', periods=100))

# Optionnel: benchmark (SPY)
benchmark = pd.Series([...])

metrics = calculate_metrics(
    equity=equity,
    benchmark=benchmark,
    risk_free_rate=0.02
)

# Returns: {
#     'total_return': 0.156,
#     'cagr': 0.052,
#     'sharpe_ratio': 0.847,
#     'sortino_ratio': 1.234,
#     'max_drawdown': -0.089,
#     'calmar_ratio': 0.584,
#     'volatility': 0.123,
#     'win_rate': 0.56
# }
```

**Métriques calculées**:

| Métrique | Description |
|----------|-------------|
| `total_return` | Return total de la période |
| `cagr` | Compound Annual Growth Rate |
| `sharpe_ratio` | Ratio de Sharpe (ajusté risque) |
| `sortino_ratio` | Ratio de Sortino (downside risk only) |
| `max_drawdown` | Drawdown maximum |
| `calmar_ratio` | CAGR / MaxDD |
| `volatility` | Volatilité annualisée |
| `win_rate` | Pourcentage de trades gagnants |

#### `format_backtest_summary(metrics, strategy_name)`

Formate les métriques en texte lisible.

```python
from shared.backtest_helpers import format_backtest_summary

summary = format_backtest_summary(metrics, 'EMA Crossover Strategy')
print(summary)
# EMA Crossover Strategy
# =========================
# Total Return: 15.60%
# CAGR: 5.20%
# Sharpe Ratio: 0.85
# Max Drawdown: -8.90%
# Win Rate: 56.00%
```

#### `compare_strategies(strategies, metrics_to_compare)`

Compare plusieurs stratégies côte à côte.

```python
from shared.backtest_helpers import compare_strategies

strategies = {
    'EMA Cross': equity_series_1,
    'MACD': equity_series_2,
    'Buy & Hold': equity_series_3
}

comparison_df = compare_strategies(
    strategies=strategies,
    metrics_to_compare=['sharpe_ratio', 'cagr', 'max_drawdown']
)

# Returns DataFrame avec métriques pour chaque stratégie
```

---

## Module: features

**Fichier**: `shared/features.py` (316 lignes)

### Description

Feature engineering pour le Machine Learning appliqué au trading. Calcule les retours, ajoute des indicateurs techniques, crée des labels pour la classification.

### Fonctions

#### `calculate_returns(prices, periods)`

Calcule les retours sur différentes périodes.

```python
from shared.features import calculate_returns
import pandas as pd

prices = pd.Series([...], index=pd.date_range('2020-01-01', periods=500))

returns_df = calculate_returns(
    prices=prices,
    periods=[1, 5, 10, 20]  # Jours
)

# Returns DataFrame avec colonnes:
# - return_1d: retour quotidien
# - return_5d: retour 5 jours
# - return_10d: retour 10 jours
# - return_20d: retour 20 jours
```

#### `add_technical_features(df, indicators, price_col)`

Ajoute des indicateurs techniques à un DataFrame.

```python
from shared.features import add_technical_features
import pandas as pd

# DataFrame avec OHLCV
df = pd.DataFrame({
    'open': [...],
    'high': [...],
    'low': [...],
    'close': [...],
    'volume': [...]
})

# Indicateurs à calculer
indicators = {
    'sma': {'period': 20},
    'ema': {'period': 12},
    'rsi': {'period': 14},
    'macd': {'fast': 12, 'slow': 26, 'signal': 9},
    'bollinger': {'period': 20, 'std': 2},
    'atr': {'period': 14}
}

df_with_features = add_technical_features(
    df=df,
    indicators=indicators,
    price_col='close'
)

# Ajoute les colonnes: sma_20, ema_12, rsi_14, macd, macd_signal, bb_upper, bb_lower, atr_14
```

#### `create_labels(returns, threshold, method)`

Crée des labels pour la classification ML.

```python
from shared.features import create_labels

returns = pd.Series([...])  # Retours quotidiens

# Classification binaire (Up/Down)
labels_binary = create_labels(
    returns=returns,
    threshold=0.0,
    method='binary'
)
# Returns: 0 (Down), 1 (Up)

# Classification ternaire (Down/Flat/Up)
labels_ternary = create_labels(
    returns=returns,
    threshold=0.01,  # 1% threshold
    method='ternary'
)
# Returns: 0 (Down), 1 (Flat), 2 (Up)
```

#### `walk_forward_split(df, train_size, n_splits)`

Split walk-forward pour time series cross-validation.

```python
from shared.features import walk_forward_split

df = pd.DataFrame(...)  # Vos features + target

splits = walk_forward_split(
    df=df,
    train_size=0.7,  # 70% train, 30% test
    n_splits=5
)

# Returns: List[(train_df, test_df), ...]
# Utilisation:
for train_df, test_df in splits:
    X_train, y_train = train_df[features], train_df['target']
    X_test, y_test = test_df[features], test_df['target']
    # Entraîner et évaluer...
```

---

## Module: indicators

**Fichier**: `shared/indicators.py` (263 lignes)

### Description

Indicateurs techniques personnalisés pour QuantConnect. Ces classes implémentent l'interface `Indicator` de QC pour être utilisées directement dans les algorithmes.

### Classes

#### `CustomMomentumIndicator`

Indicateur de momentum personnalisé.

```python
from shared.indicators import CustomMomentumIndicator

# Dans QCAlgorithm.Initialize()
momentum = CustomMomentumIndicator("CustomMomentum", period=20)

# Dans QCAlgorithm.OnData()
momentum.Update(time, price)

if momentum.IsReady:
    current_value = momentum.Current.Value
```

**Paramètres**:
- `name`: Nom de l'indicateur
- `period`: Période de calcul (défaut: 20)

**Formule**:
```
Momentum = Prix_t - Prix_(t-period)
```

#### `TrendStrengthIndicator`

Indicateur de force de tendance basé sur ADX.

```python
from shared.indicators import TrendStrengthIndicator

# Dans QCAlgorithm.Initialize()
trend_strength = TrendStrengthIndicator("TrendStrength", period=14)

# Dans QCAlgorithm.OnData()
trend_strength.Update(time, high, low, close)

if trend_strength.IsReady:
    strength = trend_strength.Current.Value
    # Interprétation:
    # - > 25: Trend fort
    # - 20-25: Trend modéré
    # - < 20: Pas de trend (range)
```

**Paramètres**:
- `name`: Nom de l'indicateur
- `period`: Période de calcul (défaut: 14)

**Formule** (basée sur ADX):
```
TR = Max(H-L, |H-C_prev|, |L-C_prev|)
+DM = H - H_prev si H > H_prev et H > L_prev, sinon 0
-DM = L_prev - L si L < L_prev et L < H_prev, sinon 0

ATR = SMA(TR, period)
+DI = 100 * SMA(+DM, period) / ATR
-DI = 100 * SMA(-DM, period) / ATR
DX = 100 * |+DI - -DI| / (+DI + -DI)
ADX = SMA(DX, period)
```

#### `VolatilityBandIndicator`

Bandes de volatilité personnalisées (type Bollinger).

```python
from shared.indicators import VolatilityBandIndicator

# Dans QCAlgorithm.Initialize()
vol_bands = VolatilityBandIndicator("VolBands", period=20, multiplier=2.0)

# Dans QCAlgorithm.OnData()
vol_bands.Update(time, high, low, close)

if vol_bands.IsReady:
    upper = vol_bands.UpperBand.Current.Value
    middle = vol_bands.MiddleBand.Current.Value  # SMA
    lower = vol_bands.LowerBand.Current.Value

    # Signaux:
    # - Prix > Upper: Surachat
    # - Prix < Lower: Survente
```

**Paramètres**:
- `name`: Nom de l'indicateur
- `period`: Période de la moyenne (défaut: 20)
- `multiplier`: Multiplicateur d'écart-type (défaut: 2.0)

**Formule**:
```
MiddleBand = SMA(Prix, period)
UpperBand = MiddleBand + multiplier * StdDev(Prix, period)
LowerBand = MiddleBand - multiplier * StdDev(Prix, period)
```

---

## Module: ml_utils

**Fichier**: `shared/ml_utils.py` (418 lignes)

### Description

Utilitaires pour entraîner, évaluer et persister des modèles ML dans QuantConnect. Supporte les modèles scikit-learn, XGBoost et LightGBM.

### Fonctions

#### `train_classifier(X_train, y_train, model_type, **kwargs)`

Entraîne un modèle de classification.

```python
from shared.ml_utils import train_classifier
import numpy as np

X_train = np.random.rand(1000, 20)  # 1000 échantillons, 20 features
y_train = np.random.randint(0, 2, 1000)  # Labels binaires

# Random Forest
model_rf = train_classifier(
    X_train, y_train,
    model_type='random_forest',
    n_estimators=100,
    max_depth=10
)

# XGBoost
model_xgb = train_classifier(
    X_train, y_train,
    model_type='xgboost',
    n_estimators=200,
    learning_rate=0.1
)

# Logistic Regression
model_lr = train_classifier(
    X_train, y_train,
    model_type='logistic',
    max_iter=1000
)
```

**Types de modèles supportés**:
- `random_forest`: RandomForestClassifier (scikit-learn)
- `xgboost`: XGBClassifier (requiert xgboost)
- `lightgbm`: LGBMClassifier (requiert lightgbm)
- `logistic`: LogisticRegression (scikit-learn)

#### `train_regressor(X_train, y_train, model_type, **kwargs)`

Entraîne un modèle de régression.

```python
from shared.ml_utils import train_regressor

X_train = np.random.rand(1000, 20)
y_train = np.random.rand(1000)  # Targets continus

# Random Forest Regressor
model_rf = train_regressor(
    X_train, y_train,
    model_type='random_forest',
    n_estimators=100
)

# XGBoost Regressor
model_xgb = train_regressor(
    X_train, y_train,
    model_type='xgboost',
    n_estimators=200
)

# SVR
model_svr = train_regressor(
    X_train, y_train,
    model_type='svr',
    kernel='rbf',
    C=1.0
)
```

#### `evaluate_model(model, X_test, y_test, task)`

Évalue un modèle ML.

```python
from shared.ml_utils import evaluate_model

# Classification
metrics_clf = evaluate_model(
    model=model_rf,
    X_test=X_test,
    y_test=y_test,
    task='classification'
)
# Returns: {
#     'accuracy': 0.85,
#     'precision': 0.87,
#     'recall': 0.83,
#     'f1_score': 0.85,
#     'sharpe_ratio': 1.23  # Si predict_proba disponible
# }

# Régression
metrics_reg = evaluate_model(
    model=model_xgb,
    X_test=X_test,
    y_test=y_test,
    task='regression'
)
# Returns: {
#     'mae': 0.012,
#     'mse': 0.0003,
#     'rmse': 0.017,
#     'r2': 0.78
# }
```

#### `save_to_objectstore(model, name, qc_algorithm, local_path)`

Sauvegarde un modèle dans ObjectStore QC ou localement.

```python
from shared.ml_utils import save_to_objectstore

# Dans QuantConnect (avec instance QCAlgorithm)
save_to_objectstore(
    model=model_rf,
    name='my_random_forest',
    qc_algorithm=self  # self = QCAlgorithm instance
)
# Returns: 'ObjectStore:my_random_forest.pkl'

# En local (hors QuantConnect)
save_to_objectstore(
    model=model_rf,
    name='my_random_forest',
    local_path='./models/my_rf_model.pkl'
)
# Returns: './models/my_rf_model.pkl'
```

#### `load_from_objectstore(name, qc_algorithm, local_path)`

Charge un modèle depuis ObjectStore QC ou localement.

```python
from shared.ml_utils import load_from_objectstore

# Dans QuantConnect
model = load_from_objectstore(
    name='my_random_forest',
    qc_algorithm=self
)

# En local
model = load_from_objectstore(
    name='my_random_forest',
    local_path='./models/my_rf_model.pkl'
)
```

#### `cross_validate_walk_forward(model_factory, X, y, n_splits, train_size_ratio)`

Cross-validation walk-forward pour time series.

```python
from shared.ml_utils import cross_validate_walk_forward
from sklearn.ensemble import RandomForestClassifier

# Factory function pour créer des modèles
def model_factory():
    return RandomForestClassifier(n_estimators=50, random_state=42)

results = cross_validate_walk_forward(
    model_factory=model_factory,
    X=X,
    y=y,
    n_splits=5,
    train_size_ratio=0.7
)

# Returns: {
#     'mean_accuracy': 0.82,
#     'std_accuracy': 0.03,
#     'n_splits_completed': 5
# }
```

---

## Module: plotting

**Fichier**: `shared/plotting.py` (332 lignes)

### Description

Visualisations standardisées pour résultats de backtests, ML et features. Utilise matplotlib et seaborn pour des graphiques cohérents.

### Fonctions

#### `plot_backtest_results(results, benchmark, title)`

Graphique complet de résultats de backtest.

```python
from shared.plotting import plot_backtest_results
import pandas as pd

# Préparer les données
results = pd.DataFrame({
    'equity': [...],      # Valeur portefeuille
    'daily_returns': [...],  # Retours quotidiens
    'drawdown': [...]     # Drawdown
}, index=pd.date_range('2020-01-01', periods=500))

# Optionnel: benchmark
benchmark = pd.Series([...])  # SPY par exemple

plot_backtest_results(
    results=results,
    benchmark=benchmark,
    title='EMA Crossover Strategy'
)
```

**Affiche 3 sous-graphiques**:
1. Equity Curve (strategy vs benchmark)
2. Drawdown
3. Returns Distribution

#### `plot_feature_importance(model, feature_names, top_n, title)`

Graphique d'importance des features (tree-based models).

```python
from shared.plotting import plot_feature_importance

plot_feature_importance(
    model=model_rf,
    feature_names=['RSI', 'MACD', 'EMA_20', 'ATR', 'Volume', ...],
    top_n=20,
    title='Feature Importance - Random Forest'
)
```

#### `plot_confusion_matrix(y_true, y_pred, labels, title)`

Matrice de confusion pour classification.

```python
from shared.plotting import plot_confusion_matrix

plot_confusion_matrix(
    y_true=y_test,
    y_pred=predictions,
    labels=['Down', 'Up'],
    title='Confusion Matrix - Direction Prediction'
)
```

#### `plot_returns_distribution(returns, title, bins)`

Distribution des retours avec statistiques.

```python
from shared.plotting import plot_returns_distribution

returns = pd.Series([...])  # Retours quotidiens

plot_returns_distribution(
    returns=returns,
    title='Daily Returns Distribution',
    bins=50
)
```

**Affiche**:
- Histogram avec mean/median
- Q-Q plot (test de normalité)
- Statistiques (mean, std, skew, kurtosis, Sharpe)

#### `plot_correlation_matrix(df, method, title)`

Heatmap de matrice de corrélation.

```python
from shared.plotting import plot_correlation_matrix

df = pd.DataFrame({
    'RSI': [...],
    'MACD': [...],
    'EMA_20': [...],
    ...
})

plot_correlation_matrix(
    df=df,
    method='pearson',  # ou 'spearman', 'kendall'
    title='Feature Correlation Matrix'
)
```

#### `plot_cumulative_returns(strategy_returns, benchmark_returns, title)`

Retours cumulatifs (strategy vs benchmark).

```python
from shared.plotting import plot_cumulative_returns

strategy_returns = pd.Series([...])  # Retours quotidiens strategy
benchmark_returns = pd.Series([...])  # Retours quotidiens benchmark

plot_cumulative_returns(
    strategy_returns=strategy_returns,
    benchmark_returns=benchmark_returns,
    title='Cumulative Returns Comparison'
)
```

---

## Workflows Courants

### Workflow 1: Backtest et Analyse

```python
import sys
sys.path.insert(0, '/Content/MyIA.AI.Notebooks/QuantConnect')

from shared.backtest_helpers import default_backtest_config, calculate_metrics, format_backtest_summary
from shared.plotting import plot_backtest_results
import pandas as pd

# 1. Configuration
config = default_backtest_config(
    start='2020-01-01',
    end='2023-12-31',
    initial_capital=100000
)

# 2. Exécuter backtest (hypothétique)
# equity_curve = ... (résultats du backtest)

# 3. Calculer métriques
metrics = calculate_metrics(equity_curve)

# 4. Afficher résumé
print(format_backtest_summary(metrics, 'My Strategy'))

# 5. Visualiser
results_df = pd.DataFrame({
    'equity': equity_curve,
    'daily_returns': equity_curve.pct_change(),
    'drawdown': (equity_curve / equity_curve.cummax()) - 1
})
plot_backtest_results(results_df)
```

### Workflow 2: Feature Engineering + ML

```python
import sys
sys.path.insert(0, '/Content/MyIA.AI.Notebooks/QuantConnect')

from shared.features import calculate_returns, add_technical_features, create_labels, walk_forward_split
from shared.ml_utils import train_classifier, evaluate_model, cross_validate_walk_forward
from shared.plotting import plot_feature_importance, plot_confusion_matrix
import pandas as pd
import numpy as np

# 1. Charger données
df = pd.DataFrame(...)  # OHLCV data

# 2. Feature engineering
indicators_config = {
    'sma': {'period': 20},
    'ema': {'period': 12},
    'rsi': {'period': 14},
    'macd': {'fast': 12, 'slow': 26, 'signal': 9}
}
df = add_technical_features(df, indicators_config)

# 3. Calculer retours et labels
df['returns'] = calculate_returns(df['close'], periods=[1])['return_1d']
df['label'] = create_labels(df['returns'], threshold=0.0, method='binary')

# 4. Split walk-forward
splits = walk_forward_split(df.dropna(), train_size=0.7, n_splits=5)

# 5. Entraîner et évaluer
for i, (train_df, test_df) in enumerate(splits):
    feature_cols = [c for c in df.columns if c.startswith(('sma_', 'ema_', 'rsi_', 'macd_'))]

    model = train_classifier(
        train_df[feature_cols].values,
        train_df['label'].values,
        model_type='random_forest'
    )

    metrics = evaluate_model(
        model,
        test_df[feature_cols].values,
        test_df['label'].values,
        task='classification'
    )

    print(f"Split {i+1}: Accuracy={metrics['accuracy']:.3f}")

# 6. Visualiser
plot_feature_importance(model, feature_cols, top_n=15)
plot_confusion_matrix(y_test, model.predict(X_test), labels=['Down', 'Up'])
```

### Workflow 3: Indicateurs Custom dans QC

```python
from AlgorithmImports import *
from shared.indicators import TrendStrengthIndicator, VolatilityBandIndicator

class MyCustomIndicatorAlgorithm(QCAlgorithm):
    def initialize(self):
        self.set_start_date(2020, 1, 1)
        self.set_cash(100000)

        # Ajouter equity
        equity = self.add_equity("SPY", Resolution.DAILY)

        # Créer indicateurs custom
        self.trend_strength = TrendStrengthIndicator("TrendStrength", 14)
        self.vol_bands = VolatilityBandIndicator("VolBands", 20, 2.0)

        # Enregistrer indicateurs
        self.register_indicator(equity.symbol, self.trend_strength, Resolution.DAILY)
        self.register_indicator(equity.symbol, self.vol_bands, Resolution.DAILY)

        # Schedule rebalance
        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance
        )

    def rebalance(self):
        if not self.trend_strength.is_ready or not self.vol_bands.is_ready:
            return

        price = self.securities["SPY"].price
        trend = self.trend_strength.current.value
        upper_band = self.vol_bands.upper_band.current.value
        lower_band = self.vol_bands.lower_band.current.value

        # Logique de trading
        if trend > 25 and price < lower_band:
            self.set_holdings("SPY", 1.0)
            self.log(f"LONG: Trend={trend:.2f}, Price < LowerBand")
        elif trend < 20 and price > upper_band:
            self.liquidate("SPY")
            self.log(f"EXIT: Trend={trend:.2f}, Price > UpperBand")
```

### Workflow 4: Persistance de Modèle

```python
import sys
sys.path.insert(0, '/Content/MyIA.AI.Notebooks/QuantConnect')

from shared.ml_utils import train_classifier, save_to_objectstore, load_from_objectstore
import numpy as np

# 1. Entraîner modèle
X_train = np.random.rand(1000, 20)
y_train = np.random.randint(0, 2, 1000)
model = train_classifier(X_train, y_train, model_type='xgboost')

# 2. Sauvegarder dans ObjectStore QC
# (Dans un notebook avec QuantBook)
# save_to_objectstore(model, 'my_xgb_model', qc_algorithm=qb)

# OU sauvegarder localement
save_to_objectstore(model, 'my_xgb_model', local_path='./models/xgb_model.pkl')

# 3. Charger plus tard
model_loaded = load_from_objectstore('my_xgb_model', local_path='./models/xgb_model.pkl')

# 4. Utiliser pour prédiction
predictions = model_loaded.predict(X_test)
```

---

## Bonnes Pratiques

### 1. Structure de Projet

```
MyProject/
├── main.py              # Algorithme principal QC
├── research.ipynb       # Notebook de recherche
├── quantbook.ipynb      # Notebook QuantBook (optionnel)
└── shared/              # Librairie partagée (importée)
    ├── __init__.py
    ├── backtest_helpers.py
    ├── features.py
    ├── indicators.py
    ├── ml_utils.py
    └── plotting.py
```

### 2. Imports Standards

```python
# Au début de chaque notebook/algorithme
import sys
sys.path.insert(0, '/Content/MyIA.AI.Notebooks/QuantConnect')

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt

from shared import features, ml_utils, plotting, backtest_helpers
```

### 3. Gestion des Données

```python
# Toujours vérifier les données manquantes
df = df.dropna()

# Normaliser les features avant ML
from sklearn.preprocessing import StandardScaler
scaler = StandardScaler()
X_scaled = scaler.fit_transform(X)
```

### 4. Validation

```python
# TOUJOURS utiliser walk-forward pour time series
# (Pas de standard K-Fold qui cause look-ahead bias)
splits = walk_forward_split(df, train_size=0.7, n_splits=5)

# TOUJOURS garder un test set final non-utilisé pour validation finale
train_val_df, test_df = split_data(df, test_size=0.2)
```

### 5. Logging

```python
# Dans les algorithmes QC
self.log(f"REBALANCE: {len(bullish)} stocks bullish")

# Dans les notebooks
print(f"Split {i+1}/{n_splits}: Accuracy={metrics['accuracy']:.3f}")
```

### 6. Performance

```python
# Pour les gros datasets, utiliser des générateurs
def batch_generator(X, y, batch_size=32):
    for i in range(0, len(X), batch_size):
        yield X[i:i+batch_size], y[i:i+batch_size]

# Éviter les boucles Python, préférer vectorisation
# ❌ Mauvais
returns = []
for i in range(1, len(prices)):
    returns.append(prices[i] / prices[i-1] - 1)

# ✅ Bon
returns = prices.pct_change().dropna()
```

---

## Ressources Supplémentaires

### Documentation QuantConnect

- [Algorithm Reference](https://www.quantconnect.com/docs)
- [API Reference](https://www.quantconnect.com/docs/api-reference)
- [Community Forum](https://www.quantconnect.com/forum)

### Tutoriels Connexes

- [SESSION5_PATTERNS.md](../projects/SESSION5_PATTERNS.md) - AlphaModel Framework
- [README.md](../projects/README.md) - Stratégies QuantConnect
- [HANDSON_AI_TRADING_MAPPING.md](../HANDSON_AI_TRADING_MAPPING.md) - Mapping notebooks projets

### Contribution

Pour ajouter de nouvelles fonctions à la librairie shared/:

1. Ajouter la fonction dans le module approprié
2. Inclure docstring avec Args/Returns/Example
3. Ajouter des tests dans `if __name__ == '__main__'`
4. Mettre à jour ce fichier (SHARED_LIBRARY.md)

---

## Changelog

### Version 1.0.0 (2026-03-23)

- **backtest_helpers.py**: Configuration et analyse de backtests
- **features.py**: Feature engineering pour ML
- **indicators.py**: 3 indicateurs custom QC
- **ml_utils.py**: Training, évaluation et persistence ML
- **plotting.py**: 6 fonctions de visualisation standardisées

---

**Fin de la documentation**

Pour toute question ou problème, consulter le [README.md](../README.md) principal ou ouvrir une issue sur le dépôt GitHub.
