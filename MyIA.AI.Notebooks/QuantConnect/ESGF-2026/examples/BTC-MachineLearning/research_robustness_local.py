"""
BTC-MachineLearning Robustness Research (Local Execution)

This script runs the same analysis as research_robustness.ipynb but using
local data instead of QuantConnect QuantBook.

To execute in QuantConnect:
1. Upload research_robustness.ipynb to the project
2. Open Research environment
3. Run cells sequentially
"""

import pandas as pd
import numpy as np
from datetime import datetime, timedelta
from sklearn.ensemble import RandomForestClassifier
from sklearn.metrics import accuracy_score
import matplotlib.pyplot as plt
import seaborn as sns
import json
import warnings
warnings.filterwarnings('ignore')

print("="*80)
print("BTC-MachineLearning Robustness Research (Local Mode)")
print("="*80)
print()
print("NOTE: This is a demonstration script using mock/sample data.")
print("For actual QuantConnect data, execute research_robustness.ipynb in QC Research.")
print()

# Mock BTC data (for demonstration purposes)
# In production, this would come from QuantBook
print("Loading sample BTC data (2017-present)...")
print("⚠️ Using mock data for demonstration - replace with actual QC data")

# Create synthetic BTC-like data
np.random.seed(42)
dates = pd.date_range(start='2017-01-01', end=datetime.now(), freq='D')
n_days = len(dates)

# Simulate BTC price with trends
base_price = 1000
prices = [base_price]
for i in range(1, n_days):
    # Add trend and noise
    trend = 0.002 if i < 365 else (-0.001 if i < 730 else 0.0015)
    noise = np.random.randn() * 0.03
    new_price = prices[-1] * (1 + trend + noise)
    prices.append(max(100, new_price))  # Floor at $100

df = pd.DataFrame({
    'close': prices,
    'high': [p * (1 + abs(np.random.randn() * 0.01)) for p in prices],
    'low': [p * (1 - abs(np.random.randn() * 0.01)) for p in prices],
    'volume': np.random.randint(1e9, 1e10, n_days)
}, index=dates)

print(f"Data loaded: {len(df)} bars from {df.index[0].date()} to {df.index[-1].date()}")
print(f"Price range: ${df['close'].min():.2f} to ${df['close'].max():.2f}")
print()

# Feature Engineering
def compute_features(df_input):
    """Compute the 9 ML features."""
    df = df_input.copy()
    features = pd.DataFrame(index=df.index)

    # 1. SMA ratio
    features['sma_ratio'] = df['close'] / df['close'].rolling(20).mean()

    # 2. RSI
    delta = df['close'].diff()
    gain = delta.where(delta > 0, 0)
    loss = -delta.where(delta < 0, 0)
    avg_gain = gain.rolling(14).mean()
    avg_loss = loss.rolling(14).mean()
    rs = avg_gain / avg_loss.replace(0, 1e-10)
    features['rsi'] = 100 - (100 / (1 + rs))

    # 3. Daily return
    features['daily_return'] = df['close'].pct_change()

    # 4-7. EMA ratios
    for period in [10, 20, 50, 200]:
        ema = df['close'].ewm(span=period, adjust=False).mean()
        features[f'ema_{period}'] = ema / df['close']

    # 8-9. ADX + ATR
    high_low = df['high'] - df['low']
    high_close = (df['high'] - df['close'].shift()).abs()
    low_close = (df['low'] - df['close'].shift()).abs()
    true_range = pd.concat([high_low, high_close, low_close], axis=1).max(axis=1)
    features['adx'] = true_range.rolling(14).mean()
    features['atr'] = true_range.rolling(14).mean() / df['close']

    # Label
    features['label'] = (df['close'].shift(-1) > df['close']).astype(int)

    return features.dropna()

print("Computing features...")
features_df = compute_features(df)
print(f"Features computed: {len(features_df)} samples")
print(f"Label distribution: {dict(features_df['label'].value_counts())}")
print()

# Walk-Forward Validation
def walk_forward_validation(features, train_days=730, test_days=90, retrain_interval=60):
    """Walk-forward validation."""
    results = []
    feature_cols = [c for c in features.columns if c != 'label']

    idx = 0
    window_num = 0

    while idx + train_days + test_days <= len(features):
        window_num += 1

        train_slice = features.iloc[idx:idx+train_days]
        test_slice = features.iloc[idx+train_days:idx+train_days+test_days]

        X_train = train_slice[feature_cols].values
        y_train = train_slice['label'].values
        X_test = test_slice[feature_cols].values
        y_test = test_slice['label'].values

        model = RandomForestClassifier(n_estimators=100, max_depth=5, random_state=42)
        model.fit(X_train, y_train)

        y_proba = model.predict_proba(X_test)[:, 1]
        y_pred = (y_proba > 0.5).astype(int)

        accuracy = accuracy_score(y_test, y_pred)

        signals = (y_proba > 0.6).astype(float) * y_proba
        returns = test_slice['daily_return'].values
        strategy_returns = returns[1:] * signals[:-1]

        mean_ret = strategy_returns.mean() * 365
        std_ret = strategy_returns.std() * np.sqrt(365)
        sharpe = mean_ret / std_ret if std_ret > 0 else 0

        cumulative = (1 + strategy_returns).cumprod()
        total_return = cumulative[-1] - 1 if len(cumulative) > 0 else 0

        results.append({
            'window': window_num,
            'test_start': test_slice.index[0],
            'test_end': test_slice.index[-1],
            'accuracy': accuracy,
            'sharpe': sharpe,
            'total_return': total_return
        })

        print(f"Window {window_num}: {test_slice.index[0].date()} → {test_slice.index[-1].date()} | "
              f"Sharpe: {sharpe:.3f} | Acc: {accuracy:.2%}")

        idx += retrain_interval

    return pd.DataFrame(results)

print("="*80)
print("WALK-FORWARD VALIDATION (Train: 730d, Test: 90d, Retrain: 60d)")
print("="*80)
print()

wf_results = walk_forward_validation(features_df, train_days=730, test_days=90, retrain_interval=60)

print()
print("="*80)
print("WALK-FORWARD SUMMARY")
print("="*80)
print(f"Total windows: {len(wf_results)}")
print(f"Average Sharpe: {wf_results['sharpe'].mean():.3f} ± {wf_results['sharpe'].std():.3f}")
print(f"Median Sharpe: {wf_results['sharpe'].median():.3f}")
print(f"Best Sharpe: {wf_results['sharpe'].max():.3f}")
print(f"Worst Sharpe: {wf_results['sharpe'].min():.3f}")
print(f"Positive Sharpe windows: {(wf_results['sharpe'] > 0).sum()} / {len(wf_results)}")
print(f"Average accuracy: {wf_results['accuracy'].mean():.2%}")
print()

# Retraining frequency comparison
print("="*80)
print("RETRAINING FREQUENCY COMPARISON")
print("="*80)
print()

retrain_intervals = [30, 60, 90]
retrain_comparison = []

for interval in retrain_intervals:
    print(f"Testing interval: {interval} days...")
    wf = walk_forward_validation(features_df, train_days=730, test_days=90, retrain_interval=interval)

    retrain_comparison.append({
        'interval': interval,
        'n_windows': len(wf),
        'mean_sharpe': wf['sharpe'].mean(),
        'std_sharpe': wf['sharpe'].std(),
        'positive_pct': (wf['sharpe'] > 0).sum() / len(wf) * 100
    })
    print()

retrain_df = pd.DataFrame(retrain_comparison).set_index('interval')
print(retrain_df)
print()

# Recommendations
best_interval = retrain_df['mean_sharpe'].idxmax()
print("="*80)
print("RECOMMENDATIONS")
print("="*80)
print(f"✓ Optimal retraining interval: {best_interval} days")
print(f"  Mean Sharpe: {retrain_df.loc[best_interval, 'mean_sharpe']:.3f}")
print(f"  Positive windows: {retrain_df.loc[best_interval, 'positive_pct']:.1f}%")
print()

recommendations = {
    "research_date": datetime.now().strftime("%Y-%m-%d"),
    "project": "BTC-MachineLearning (21047688)",
    "methodology": "Walk-forward validation",
    "findings": {
        "walk_forward": {
            "total_windows": len(wf_results),
            "mean_sharpe": round(wf_results['sharpe'].mean(), 3),
            "positive_windows_pct": round((wf_results['sharpe'] > 0).sum() / len(wf_results) * 100, 1)
        },
        "optimal_retraining": {
            "interval_days": int(best_interval),
            "mean_sharpe": round(retrain_df.loc[best_interval, 'mean_sharpe'], 3)
        }
    },
    "recommendations": [
        f"Use retraining interval of {best_interval} days",
        "Execute full notebook in QuantConnect Research for real data",
        "Validate with extended training period (2017-2022)",
        "Compare feature importance across regimes"
    ]
}

print("Recommendations JSON:")
print(json.dumps(recommendations, indent=2))
print()
print("="*80)
print("NEXT STEPS")
print("="*80)
print("1. Upload research_robustness.ipynb to QuantConnect project 21047688")
print("2. Open Research environment in QuantConnect")
print("3. Execute notebook cells sequentially with real BTC data")
print("4. Update main.py based on findings")
print("5. Compile and backtest")
print()
print("NOTE: This local script uses synthetic data for demonstration.")
print("Real results will differ when executed in QuantConnect Research.")
