"""
Plotting Utilities pour QuantConnect

Visualisations standardisées pour résultats de backtests, ML, features.
Utilisées dans tous les notebooks pour visualisations cohérentes.

Fonctions:
    - plot_backtest_results: Graphiques backtest (equity curve, drawdown, etc.)
    - plot_feature_importance: Feature importance pour modèles tree-based
    - plot_confusion_matrix: Matrice de confusion classification
    - plot_returns_distribution: Distribution des retours
    - plot_correlation_matrix: Heatmap corrélations

Usage:
    from shared.plotting import plot_backtest_results, plot_feature_importance

    plot_backtest_results(results_df, benchmark_series)
    plot_feature_importance(model, feature_names)
"""

import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
import numpy as np
from typing import Optional, List, Dict


def plot_backtest_results(results: pd.DataFrame,
                          benchmark: Optional[pd.Series] = None,
                          title: str = 'Backtest Results'):
    """
    Plot résultats de backtest (equity curve, drawdown, returns distribution)

    Args:
        results: DataFrame avec 'equity', 'daily_returns', 'drawdown'
        benchmark: Série benchmark (ex: SPY) pour comparaison
        title: Titre du graphique

    Example:
        >>> import pandas as pd
        >>> import numpy as np
        >>> dates = pd.date_range('2020-01-01', periods=100)
        >>> equity = pd.Series(np.cumsum(np.random.randn(100) * 0.01) + 100, index=dates)
        >>> results = pd.DataFrame({'equity': equity})
        >>> results['daily_returns'] = results['equity'].pct_change()
        >>> results['drawdown'] = (results['equity'] / results['equity'].cummax()) - 1
        >>> plot_backtest_results(results)
        >>> plt.close('all')
    """
    fig, axes = plt.subplots(3, 1, figsize=(14, 10))
    fig.suptitle(title, fontsize=16, fontweight='bold')

    # 1. Equity Curve
    ax1 = axes[0]
    ax1.plot(results.index, results['equity'], label='Strategy', linewidth=2)

    if benchmark is not None and len(benchmark) > 0:
        # Normaliser benchmark au même starting point
        benchmark_norm = benchmark / benchmark.iloc[0] * results['equity'].iloc[0]
        ax1.plot(benchmark.index, benchmark_norm, label='Benchmark',
                linewidth=2, alpha=0.7, linestyle='--')

    ax1.set_ylabel('Portfolio Value ($)', fontsize=12)
    ax1.set_title('Equity Curve', fontsize=14, fontweight='bold')
    ax1.legend(loc='best')
    ax1.grid(True, alpha=0.3)

    # 2. Drawdown
    ax2 = axes[1]
    ax2.fill_between(results.index, results['drawdown'] * 100, 0,
                     color='red', alpha=0.3, label='Drawdown')
    ax2.plot(results.index, results['drawdown'] * 100, color='darkred', linewidth=1.5)
    ax2.set_ylabel('Drawdown (%)', fontsize=12)
    ax2.set_title('Drawdown', fontsize=14, fontweight='bold')
    ax2.legend(loc='best')
    ax2.grid(True, alpha=0.3)

    # 3. Returns Distribution
    ax3 = axes[2]
    returns = results['daily_returns'].dropna()
    ax3.hist(returns * 100, bins=50, alpha=0.7, color='skyblue', edgecolor='black')
    ax3.axvline(returns.mean() * 100, color='red', linestyle='--',
               linewidth=2, label=f'Mean: {returns.mean()*100:.2f}%')
    ax3.set_xlabel('Daily Returns (%)', fontsize=12)
    ax3.set_ylabel('Frequency', fontsize=12)
    ax3.set_title('Returns Distribution', fontsize=14, fontweight='bold')
    ax3.legend(loc='best')
    ax3.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.show()


def plot_feature_importance(model,
                           feature_names: List[str],
                           top_n: int = 20,
                           title: str = 'Feature Importance'):
    """
    Plot feature importance pour modèles tree-based

    Args:
        model: Modèle avec .feature_importances_
        feature_names: Noms des features
        top_n: Nombre de top features à afficher
        title: Titre du graphique

    Example:
        >>> from sklearn.ensemble import RandomForestClassifier
        >>> import numpy as np
        >>> X = np.random.rand(100, 10)
        >>> y = np.random.randint(0, 2, 100)
        >>> model = RandomForestClassifier(n_estimators=10, random_state=42)
        >>> model.fit(X, y)
        >>> plot_feature_importance(model, [f'feature_{i}' for i in range(10)], top_n=5)
        >>> plt.close('all')
    """
    if not hasattr(model, 'feature_importances_'):
        raise ValueError("Model must have .feature_importances_ attribute")

    # Créer DataFrame importance
    importance_df = pd.DataFrame({
        'feature': feature_names,
        'importance': model.feature_importances_
    }).sort_values('importance', ascending=False).head(top_n)

    # Plot
    plt.figure(figsize=(12, max(6, top_n * 0.3)))
    plt.barh(range(len(importance_df)), importance_df['importance'], color='skyblue')
    plt.yticks(range(len(importance_df)), importance_df['feature'])
    plt.xlabel('Importance', fontsize=12)
    plt.title(title, fontsize=14, fontweight='bold')
    plt.gca().invert_yaxis()
    plt.grid(True, alpha=0.3, axis='x')
    plt.tight_layout()
    plt.show()


def plot_confusion_matrix(y_true, y_pred, labels: Optional[List[str]] = None,
                         title: str = 'Confusion Matrix'):
    """
    Plot matrice de confusion

    Args:
        y_true: Labels vrais
        y_pred: Labels prédits
        labels: Noms des classes
        title: Titre du graphique

    Example:
        >>> import numpy as np
        >>> y_true = np.array([0, 1, 0, 1, 0, 1])
        >>> y_pred = np.array([0, 1, 0, 0, 0, 1])
        >>> plot_confusion_matrix(y_true, y_pred, labels=['Down', 'Up'])
        >>> plt.close('all')
    """
    from sklearn.metrics import confusion_matrix

    # Calculer matrice
    cm = confusion_matrix(y_true, y_pred)

    # Plot
    plt.figure(figsize=(8, 6))
    sns.heatmap(cm, annot=True, fmt='d', cmap='Blues',
               xticklabels=labels if labels else range(cm.shape[0]),
               yticklabels=labels if labels else range(cm.shape[1]),
               cbar_kws={'label': 'Count'})
    plt.xlabel('Predicted', fontsize=12)
    plt.ylabel('True', fontsize=12)
    plt.title(title, fontsize=14, fontweight='bold')
    plt.tight_layout()
    plt.show()


def plot_returns_distribution(returns: pd.Series,
                             title: str = 'Returns Distribution',
                             bins: int = 50):
    """
    Plot distribution des retours avec stats

    Args:
        returns: Série de retours
        title: Titre du graphique
        bins: Nombre de bins histogram

    Example:
        >>> import pandas as pd
        >>> import numpy as np
        >>> returns = pd.Series(np.random.randn(1000) * 0.02)
        >>> plot_returns_distribution(returns)
        >>> plt.close('all')
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    fig.suptitle(title, fontsize=16, fontweight='bold')

    # 1. Histogram
    ax1 = axes[0]
    ax1.hist(returns * 100, bins=bins, alpha=0.7, color='skyblue', edgecolor='black')
    ax1.axvline(returns.mean() * 100, color='red', linestyle='--',
               linewidth=2, label=f'Mean: {returns.mean()*100:.2f}%')
    ax1.axvline(returns.median() * 100, color='green', linestyle='--',
               linewidth=2, label=f'Median: {returns.median()*100:.2f}%')
    ax1.set_xlabel('Returns (%)', fontsize=12)
    ax1.set_ylabel('Frequency', fontsize=12)
    ax1.set_title('Histogram', fontsize=12)
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # 2. Q-Q Plot
    from scipy import stats
    ax2 = axes[1]
    stats.probplot(returns, dist="norm", plot=ax2)
    ax2.set_title('Q-Q Plot (Normality)', fontsize=12)
    ax2.grid(True, alpha=0.3)

    # Stats texte
    stats_text = (
        f"Mean: {returns.mean()*100:.2f}%\n"
        f"Std: {returns.std()*100:.2f}%\n"
        f"Skew: {returns.skew():.2f}\n"
        f"Kurtosis: {returns.kurtosis():.2f}\n"
        f"Sharpe (daily): {returns.mean() / returns.std():.2f}"
    )
    plt.figtext(0.99, 0.5, stats_text, fontsize=10,
               bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5),
               ha='right', va='center')

    plt.tight_layout()
    plt.show()


def plot_correlation_matrix(df: pd.DataFrame,
                           method: str = 'pearson',
                           title: str = 'Correlation Matrix'):
    """
    Plot heatmap matrice de corrélations

    Args:
        df: DataFrame avec features numériques
        method: 'pearson', 'spearman', ou 'kendall'
        title: Titre du graphique

    Example:
        >>> import pandas as pd
        >>> import numpy as np
        >>> df = pd.DataFrame(np.random.rand(100, 5), columns=[f'f{i}' for i in range(5)])
        >>> plot_correlation_matrix(df)
        >>> plt.close('all')
    """
    # Calculer corrélations
    corr = df.corr(method=method)

    # Plot
    plt.figure(figsize=(10, 8))
    sns.heatmap(corr, annot=True, fmt='.2f', cmap='coolwarm',
               center=0, vmin=-1, vmax=1,
               square=True, linewidths=0.5,
               cbar_kws={'label': 'Correlation'})
    plt.title(title, fontsize=14, fontweight='bold')
    plt.tight_layout()
    plt.show()


def plot_cumulative_returns(strategy_returns: pd.Series,
                           benchmark_returns: Optional[pd.Series] = None,
                           title: str = 'Cumulative Returns'):
    """
    Plot retours cumulatifs (strategy vs benchmark)

    Args:
        strategy_returns: Série de retours strategy
        benchmark_returns: Série de retours benchmark (optionnel)
        title: Titre du graphique

    Example:
        >>> import pandas as pd
        >>> import numpy as np
        >>> dates = pd.date_range('2020-01-01', periods=100)
        >>> strategy_ret = pd.Series(np.random.randn(100) * 0.01, index=dates)
        >>> plot_cumulative_returns(strategy_ret)
        >>> plt.close('all')
    """
    # Calculer retours cumulatifs
    cum_returns_strategy = (1 + strategy_returns).cumprod()

    plt.figure(figsize=(14, 6))
    plt.plot(cum_returns_strategy.index, cum_returns_strategy,
            label='Strategy', linewidth=2)

    if benchmark_returns is not None:
        cum_returns_benchmark = (1 + benchmark_returns).cumprod()
        plt.plot(cum_returns_benchmark.index, cum_returns_benchmark,
                label='Benchmark', linewidth=2, alpha=0.7, linestyle='--')

    plt.xlabel('Date', fontsize=12)
    plt.ylabel('Cumulative Returns', fontsize=12)
    plt.title(title, fontsize=14, fontweight='bold')
    plt.legend(loc='best')
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.show()


if __name__ == '__main__':
    # Tests rapides
    print("Testing plotting.py...")
    import warnings
    warnings.filterwarnings('ignore')

    # Créer données test
    dates = pd.date_range('2020-01-01', periods=100)
    equity = pd.Series(np.cumsum(np.random.randn(100) * 0.01) + 100, index=dates)
    results = pd.DataFrame({'equity': equity})
    results['daily_returns'] = results['equity'].pct_change()
    results['drawdown'] = (results['equity'] / results['equity'].cummax()) - 1

    # Test plot_backtest_results
    print("✓ Testing plot_backtest_results...")
    plot_backtest_results(results)
    plt.close('all')

    # Test plot_feature_importance
    from sklearn.ensemble import RandomForestClassifier
    X = np.random.rand(100, 5)
    y = np.random.randint(0, 2, 100)
    model = RandomForestClassifier(n_estimators=10, random_state=42)
    model.fit(X, y)
    print("✓ Testing plot_feature_importance...")
    plot_feature_importance(model, [f'feature_{i}' for i in range(5)], top_n=5)
    plt.close('all')

    print("\nAll tests passed! ✓")
