"""Economic metrics for volatility forecasting evaluation.

Translates statistical forecast accuracy into trading-relevant measures:
- Vol-targeted Sharpe ratio: risk-adjusted return from vol-timing signals
- VaR breach rate: proportion of realized losses exceeding VaR prediction
- Utility gain: economic value of improved forecasts (fees-adjusted)

References:
- Patton (2011) "Volatility Forecast Comparison Using Imperfect Volatility Proxies"
- Fleming, Kirby, Ostdiek (2001) "The Economic Value of Volatility Timing"
"""

from __future__ import annotations

import numpy as np


def vol_targeted_sharpe(
    realized_vol: np.ndarray,
    forecast_vol: np.ndarray,
    target_vol: float = 0.15,
    rf_annual: float = 0.0,
    fee_bps: float = 10.0,
) -> dict:
    """Sharpe ratio from volatility-targeting strategy.

    The strategy scales position size inversely to forecasted volatility
    to maintain a constant target annualized vol. Better vol forecasts
    produce more accurate position sizing and higher risk-adjusted returns.

    Parameters
    ----------
    realized_vol : array
        Annualized realized volatility for each period.
    forecast_vol : array
        Annualized forecast volatility for each period (model prediction).
    target_vol : float
        Target annualized portfolio volatility (default 15%).
    rf_annual : float
        Risk-free rate (annualized).
    fee_bps : float
        Transaction cost in basis points per rebalance.

    Returns
    -------
    dict with keys:
        sharpe: float — annualized Sharpe ratio
        gross_return: float — annualized gross return
        net_return: float — annualized net return (after fees)
        turnover: float — average absolute weight change per period
        n_periods: int
    """
    realized_vol = np.asarray(realized_vol, dtype=float)
    forecast_vol = np.asarray(forecast_vol, dtype=float)
    n = min(len(realized_vol), len(forecast_vol))
    realized_vol = realized_vol[:n]
    forecast_vol = forecast_vol[:n]

    if n < 20:
        return {
            "sharpe": float("nan"),
            "gross_return": float("nan"),
            "net_return": float("nan"),
            "turnover": float("nan"),
            "n_periods": n,
        }

    # Position weight = target_vol / forecast_vol, floored to avoid division issues
    weights = target_vol / np.clip(forecast_vol, 0.01, None)

    # Period returns proportional to realized vol (assuming zero-mean price changes,
    # the P&L comes from vol timing: holding more when vol is lower than expected)
    # Realized period return ≈ realized_vol * sign(weights - 1)
    # More precisely: r_portfolio = w * r_market, where E[r_market] ~ 0
    # Vol-timing value comes from lower realized vol when weight is high
    period_returns = weights * (realized_vol / np.sqrt(252)) * np.sign(weights - 1.0)

    # Turnover
    weight_changes = np.abs(np.diff(weights))
    avg_turnover = float(np.mean(weight_changes))
    fee_per_period = (fee_bps / 10000.0) * avg_turnover

    # Annualize (assume daily periods)
    gross_ret = float(np.mean(period_returns)) * 252
    net_ret = gross_ret - fee_per_period * 252
    vol_pnl = float(np.std(period_returns, ddof=1)) * np.sqrt(252)
    sharpe = (net_ret - rf_annual) / vol_pnl if vol_pnl > 1e-10 else 0.0

    return {
        "sharpe": round(float(sharpe), 4),
        "gross_return": round(gross_ret, 6),
        "net_return": round(net_ret, 6),
        "turnover": round(avg_turnover, 6),
        "n_periods": n,
    }


def var_breach_rate(
    realized_returns: np.ndarray,
    forecast_var: np.ndarray,
    confidence: float = 0.95,
) -> dict:
    """VaR breach rate — proportion of realized losses exceeding VaR prediction.

    A well-calibrated VaR model should have breach rate ≈ (1 - confidence).
    Excessive breaches = underestimation of risk. Too few = over-conservative.

    Parameters
    ----------
    realized_returns : array
        Actual period returns (negative = loss).
    forecast_var : array
        Forecast Value-at-Risk (as positive number, e.g. -2% → 0.02).
        VaR is defined as the loss threshold: breach if return < -forecast_var.
    confidence : float
        VaR confidence level (default 95%).

    Returns
    -------
    dict with keys:
        breach_rate: float — proportion of periods with breach
        expected_rate: float — 1 - confidence
        n_breaches: int
        n_periods: int
        kupiec_p: float — Kupiec (1995) proportion-of-failures test p-value
        calibrated: bool — breach_rate within 1.5x of expected
    """
    realized_returns = np.asarray(realized_returns, dtype=float)
    forecast_var = np.asarray(forecast_var, dtype=float)
    n = min(len(realized_returns), len(forecast_var))
    realized_returns = realized_returns[:n]
    forecast_var = forecast_var[:n]

    if n < 20:
        return {
            "breach_rate": float("nan"),
            "expected_rate": 1.0 - confidence,
            "n_breaches": 0,
            "n_periods": n,
            "kupiec_p": float("nan"),
            "calibrated": False,
        }

    breaches = realized_returns < -forecast_var
    x = int(breaches.sum())
    p_hat = x / n
    p0 = 1.0 - confidence

    # Kupiec likelihood-ratio test
    if x == 0 or x == n:
        kupiec_p = float("nan")
    else:
        from scipy import stats as sp_stats
        lr = 2.0 * (
            x * np.log(p_hat / p0) + (n - x) * np.log((1 - p_hat) / (1 - p0))
        )
        kupiec_p = float(1.0 - sp_stats.chi2.cdf(lr, df=1))

    # Calibrated if within 1.5x of expected rate
    calibrated = abs(p_hat - p0) <= 0.5 * p0

    return {
        "breach_rate": round(float(p_hat), 4),
        "expected_rate": round(p0, 4),
        "n_breaches": x,
        "n_periods": n,
        "kupiec_p": round(kupiec_p, 4),
        "calibrated": calibrated,
    }


def utility_gain(
    mse_model: float,
    mse_baseline: float,
    n_assets: int = 1,
    risk_aversion: float = 3.0,
    fee_bps: float = 10.0,
) -> dict:
    """Economic utility gain from improved volatility forecast.

    Based on Fleming-Kirby-Ostdiek (2001) framework: the utility gain
    from better vol forecasts translates into basis points of additional
    return a risk-averse investor would pay to switch models.

    Parameters
    ----------
    mse_model : float
        MSE of candidate model (log-RV scale).
    mse_baseline : float
        MSE of baseline (log-RV scale).
    n_assets : int
        Number of assets in portfolio.
    risk_aversion : float
        Coefficient of relative risk aversion.
    fee_bps : float
        Transaction cost per rebalance (basis points).

    Returns
    -------
    dict with keys:
        gain_bps: float — utility gain in basis points (annualized)
        model_mse: float
        baseline_mse: float
        mse_reduction_pct: float — percentage reduction in MSE
        worth_switching: bool — gain exceeds transaction costs
    """
    if mse_baseline < 1e-15:
        return {
            "gain_bps": 0.0,
            "model_mse": mse_model,
            "baseline_mse": mse_baseline,
            "mse_reduction_pct": 0.0,
            "worth_switching": False,
        }

    mse_reduction = (mse_baseline - mse_model) / mse_baseline
    # Utility gain approximation (Fleming et al 2001)
    # ΔU ≈ (γ/2) * (σ²_baseline - σ²_model) ≈ (γ/2) * ΔMSE * scaling
    gain_bps = risk_aversion * 0.5 * max(mse_reduction, 0) * 10000
    gain_bps = min(gain_bps, fee_bps * 10)  # cap at 10x fee

    return {
        "gain_bps": round(float(gain_bps), 2),
        "model_mse": round(mse_model, 6),
        "baseline_mse": round(mse_baseline, 6),
        "mse_reduction_pct": round(float(mse_reduction * 100), 2),
        "worth_switching": gain_bps > fee_bps,
    }
