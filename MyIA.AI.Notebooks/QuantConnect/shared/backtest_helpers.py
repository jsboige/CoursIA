"""
Backtest Helpers pour QuantConnect

Fonctions helper pour configuration et analyse de backtests.
Utilisées dans tous les notebooks pour setup consistant.

Fonctions:
    - default_backtest_config: Configuration backtest par défaut
    - calculate_metrics: Calcule métriques de performance
    - format_backtest_summary: Formate résumé backtest
    - compare_strategies: Compare plusieurs stratégies

Usage:
    from shared.backtest_helpers import default_backtest_config, calculate_metrics

    config = default_backtest_config(start='2020-01-01', end='2023-12-31')
    metrics = calculate_metrics(equity_curve, benchmark)
"""

import pandas as pd
import numpy as np
from typing import Dict, List, Optional
from datetime import datetime


def default_backtest_config(start: str = '2020-01-01',
                           end: str = '2023-12-31',
                           initial_capital: float = 100000,
                           resolution: str = 'Daily') -> Dict[str, any]:
    """
    Configuration backtest par défaut

    Args:
        start: Date de début (YYYY-MM-DD)
        end: Date de fin (YYYY-MM-DD)
        initial_capital: Capital initial ($)
        resolution: Résolution ('Tick', 'Second', 'Minute', 'Hour', 'Daily')

    Returns:
        Dict de configuration

    Example:
        >>> config = default_backtest_config()
        >>> config['initial_capital']
        100000
    """
    return {
        'start_date': start,
        'end_date': end,
        'initial_capital': initial_capital,
        'resolution': resolution,
        'brokerage_model': 'Default',
        'slippage_model': 'ConstantSlippage',
        'fill_model': 'ImmediateFill',
        'fee_model': 'ConstantFee',
        'benchmark': 'SPY'
    }


def calculate_metrics(equity: pd.Series,
                     benchmark: Optional[pd.Series] = None,
                     risk_free_rate: float = 0.02) -> Dict[str, float]:
    """
    Calcule métriques de performance complètes

    Args:
        equity: Série equity curve
        benchmark: Série benchmark (optionnel)
        risk_free_rate: Taux sans risque annuel (default: 2%)

    Returns:
        Dict de métriques

    Example:
        >>> import pandas as pd
        >>> import numpy as np
        >>> dates = pd.date_range('2020-01-01', periods=252)
        >>> equity = pd.Series(np.cumsum(np.random.randn(252) * 0.01) + 100, index=dates)
        >>> metrics = calculate_metrics(equity)
        >>> 'sharpe_ratio' in metrics and 'max_drawdown' in metrics
        True
    """
    # Calculer returns
    returns = equity.pct_change().dropna()

    # Métriques de base
    total_return = (equity.iloc[-1] - equity.iloc[0]) / equity.iloc[0]
    annualized_return = (1 + total_return) ** (252 / len(returns)) - 1

    # Volatilité
    volatility = returns.std() * np.sqrt(252)

    # Sharpe Ratio
    excess_returns = annualized_return - risk_free_rate
    sharpe_ratio = excess_returns / volatility if volatility > 0 else 0.0

    # Sortino Ratio (downside deviation)
    downside_returns = returns[returns < 0]
    downside_std = downside_returns.std() * np.sqrt(252)
    sortino_ratio = excess_returns / downside_std if downside_std > 0 else 0.0

    # Drawdown
    cumulative = (1 + returns).cumprod()
    running_max = cumulative.cummax()
    drawdown = (cumulative - running_max) / running_max
    max_drawdown = drawdown.min()

    # Calmar Ratio
    calmar_ratio = annualized_return / abs(max_drawdown) if max_drawdown != 0 else 0.0

    # Win rate
    win_rate = (returns > 0).sum() / len(returns) if len(returns) > 0 else 0.0

    # Alpha et Beta (si benchmark fourni)
    alpha, beta = 0.0, 1.0
    if benchmark is not None and len(benchmark) > 0:
        benchmark_returns = benchmark.pct_change().dropna()

        # Aligner les indices
        aligned_returns, aligned_benchmark = returns.align(benchmark_returns, join='inner')

        if len(aligned_returns) > 1:
            # Beta
            covariance = np.cov(aligned_returns, aligned_benchmark)[0, 1]
            benchmark_variance = aligned_benchmark.var()
            beta = covariance / benchmark_variance if benchmark_variance > 0 else 1.0

            # Alpha (annualisé)
            benchmark_return = (1 + benchmark.pct_change().mean()) ** 252 - 1
            alpha = annualized_return - (risk_free_rate + beta * (benchmark_return - risk_free_rate))

    metrics = {
        'total_return': total_return,
        'annualized_return': annualized_return,
        'volatility': volatility,
        'sharpe_ratio': sharpe_ratio,
        'sortino_ratio': sortino_ratio,
        'max_drawdown': max_drawdown,
        'calmar_ratio': calmar_ratio,
        'win_rate': win_rate,
        'alpha': alpha,
        'beta': beta,
        'total_trades': len(returns),  # Approximation
    }

    return metrics


def format_backtest_summary(metrics: Dict[str, float],
                           strategy_name: str = 'Strategy') -> str:
    """
    Formate résumé backtest en texte

    Args:
        metrics: Dict de métriques (depuis calculate_metrics)
        strategy_name: Nom de la stratégie

    Returns:
        String formaté

    Example:
        >>> metrics = {
        ...     'total_return': 0.25, 'sharpe_ratio': 1.5,
        ...     'max_drawdown': -0.15, 'win_rate': 0.55
        ... }
        >>> summary = format_backtest_summary(metrics, 'Test Strategy')
        >>> 'Total Return: 25.00%' in summary
        True
    """
    summary = f"""
{'='*60}
{strategy_name} - Backtest Summary
{'='*60}

Returns:
  Total Return:        {metrics.get('total_return', 0)*100:>8.2f}%
  Annualized Return:   {metrics.get('annualized_return', 0)*100:>8.2f}%
  Volatility (ann.):   {metrics.get('volatility', 0)*100:>8.2f}%

Risk-Adjusted:
  Sharpe Ratio:        {metrics.get('sharpe_ratio', 0):>8.2f}
  Sortino Ratio:       {metrics.get('sortino_ratio', 0):>8.2f}
  Calmar Ratio:        {metrics.get('calmar_ratio', 0):>8.2f}

Drawdown:
  Max Drawdown:        {metrics.get('max_drawdown', 0)*100:>8.2f}%

Trading:
  Win Rate:            {metrics.get('win_rate', 0)*100:>8.2f}%
  Total Trades:        {metrics.get('total_trades', 0):>8.0f}

Alpha/Beta:
  Alpha:               {metrics.get('alpha', 0)*100:>8.2f}%
  Beta:                {metrics.get('beta', 0):>8.2f}

{'='*60}
"""
    return summary


def compare_strategies(strategies: Dict[str, pd.Series],
                      metrics_to_compare: Optional[List[str]] = None) -> pd.DataFrame:
    """
    Compare plusieurs stratégies

    Args:
        strategies: Dict {name: equity_series}
        metrics_to_compare: Liste de métriques (None = toutes)

    Returns:
        DataFrame de comparaison

    Example:
        >>> import pandas as pd
        >>> import numpy as np
        >>> dates = pd.date_range('2020-01-01', periods=252)
        >>> s1 = pd.Series(np.cumsum(np.random.randn(252) * 0.01) + 100, index=dates)
        >>> s2 = pd.Series(np.cumsum(np.random.randn(252) * 0.01) + 100, index=dates)
        >>> strategies = {'Strategy 1': s1, 'Strategy 2': s2}
        >>> comparison = compare_strategies(strategies)
        >>> len(comparison)
        2
    """
    if metrics_to_compare is None:
        metrics_to_compare = [
            'total_return', 'sharpe_ratio', 'max_drawdown',
            'volatility', 'win_rate'
        ]

    comparison_data = []

    for name, equity in strategies.items():
        metrics = calculate_metrics(equity)

        row = {'strategy': name}
        for metric in metrics_to_compare:
            row[metric] = metrics.get(metric, np.nan)

        comparison_data.append(row)

    comparison_df = pd.DataFrame(comparison_data)
    comparison_df.set_index('strategy', inplace=True)

    return comparison_df


def is_trading_day(date: datetime, market: str = 'NYSE') -> bool:
    """
    Vérifie si une date est un jour de trading

    Args:
        date: Date à vérifier
        market: Marché ('NYSE', 'NASDAQ', etc.)

    Returns:
        True si trading day

    Example:
        >>> from datetime import datetime
        >>> # Lundi (trading day)
        >>> is_trading_day(datetime(2023, 1, 2))
        True
        >>> # Samedi (weekend)
        >>> is_trading_day(datetime(2023, 1, 7))
        False
    """
    # Simplification : pas weekend
    if date.weekday() >= 5:  # Samedi (5) ou Dimanche (6)
        return False

    # TODO: Ajouter jours fériés US (NYSE calendar)
    # Pour l'instant, juste check weekend

    return True


def annualized_sharpe(returns: pd.Series, risk_free_rate: float = 0.02) -> float:
    """
    Calcule Sharpe Ratio annualisé

    Args:
        returns: Série de retours (daily)
        risk_free_rate: Taux sans risque annuel

    Returns:
        Sharpe ratio

    Example:
        >>> import pandas as pd
        >>> import numpy as np
        >>> returns = pd.Series(np.random.randn(252) * 0.01)
        >>> sharpe = annualized_sharpe(returns)
        >>> isinstance(sharpe, float)
        True
    """
    if len(returns) == 0:
        return 0.0

    mean_return = returns.mean() * 252
    std_return = returns.std() * np.sqrt(252)

    if std_return == 0:
        return 0.0

    sharpe = (mean_return - risk_free_rate) / std_return
    return sharpe


if __name__ == '__main__':
    # Tests rapides
    print("Testing backtest_helpers.py...")

    # Test default_backtest_config
    config = default_backtest_config()
    print(f"✓ default_backtest_config: capital={config['initial_capital']}")

    # Test calculate_metrics
    dates = pd.date_range('2020-01-01', periods=252)
    equity = pd.Series(np.cumsum(np.random.randn(252) * 0.01) + 100, index=dates)
    metrics = calculate_metrics(equity)
    print(f"✓ calculate_metrics: Sharpe={metrics['sharpe_ratio']:.2f}, "
          f"Drawdown={metrics['max_drawdown']*100:.2f}%")

    # Test format_backtest_summary
    summary = format_backtest_summary(metrics, 'Test Strategy')
    print(f"✓ format_backtest_summary: {len(summary)} characters")

    # Test compare_strategies
    s1 = pd.Series(np.cumsum(np.random.randn(252) * 0.01) + 100, index=dates)
    s2 = pd.Series(np.cumsum(np.random.randn(252) * 0.01) + 100, index=dates)
    comparison = compare_strategies({'Strategy 1': s1, 'Strategy 2': s2})
    print(f"✓ compare_strategies: {len(comparison)} strategies compared")

    print("\nAll tests passed! ✓")
