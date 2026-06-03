"""Realized GARCH model (Hansen, Huang, Shek 2012) with custom MLE.

Extends GARCH(1,1) with a measurement equation linking latent conditional
variance to observed Realized Variance. The model jointly estimates return
dynamics and realized measure dynamics in a single MLE pass.

Model equations:
    GARCH:     h_t = omega + alpha * eps^2_{t-1} + beta * h_{t-1}
    Measure:   log(RV_t) = xi + phi * log(h_t) + tau(eps_t) + u_t
    Leverage:  tau(eps_t) = gamma_1 * eps_t + gamma_2 * (eps_t^2 - 1)

Parameters (7-9 total, all economically interpretable):
    omega  > 0   — long-run variance base
    alpha  >= 0  — shock sensitivity (ARCH term)
    beta   >= 0  — variance persistence (GARCH term)
    xi     — measurement equation intercept
    phi    > 0   — elasticity of RV to conditional variance
    sigma_u > 0  — measurement noise std dev
    gamma_1 — leverage effect (asymmetric response to sign of shock)
    gamma_2 — leverage effect (response to magnitude of shock)

Constraints: alpha + beta < 1 (stationarity), omega > 0, sigma_u > 0.

References:
- Hansen, P.R., Huang, Z. & Shek, H.H. (2012) "Realized GARCH: A Joint Model
  for Returns and Realized Measures of Volatility", J. Applied Econometrics 27(6).
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
from scipy.optimize import minimize


@dataclass
class RealizedGARCHParams:
    """Estimated Realized GARCH parameters."""
    omega: float
    alpha: float
    beta: float
    xi: float
    phi: float
    sigma_u: float
    gamma1: float
    gamma2: float

    @property
    def persistence(self) -> float:
        return self.alpha + self.beta

    def as_array(self) -> np.ndarray:
        return np.array([
            self.omega, self.alpha, self.beta,
            self.xi, self.phi, self.sigma_u,
            self.gamma1, self.gamma2,
        ])

    @classmethod
    def from_array(cls, x: np.ndarray) -> "RealizedGARCHParams":
        return cls(
            omega=x[0], alpha=x[1], beta=x[2],
            xi=x[3], phi=x[4], sigma_u=x[5],
            gamma1=x[6], gamma2=x[7],
        )


def _params_from_vec(theta: np.ndarray) -> dict:
    """Unpack parameter vector into named dict with constraints applied."""
    omega_raw, alpha_raw, beta_raw = theta[0], theta[1], theta[2]
    xi, phi_raw, sigma_u_raw = theta[3], theta[4], theta[5]
    gamma1, gamma2 = theta[6], theta[7]

    omega = np.exp(omega_raw)
    alpha = 1.0 / (1.0 + np.exp(-alpha_raw))
    beta = 1.0 / (1.0 + np.exp(-beta_raw))
    phi = np.exp(phi_raw)
    sigma_u = np.exp(sigma_u_raw)

    return {
        "omega": omega, "alpha": alpha, "beta": beta,
        "xi": xi, "phi": phi, "sigma_u": sigma_u,
        "gamma1": gamma1, "gamma2": gamma2,
    }


def _initial_params(returns: np.ndarray, rv: np.ndarray) -> np.ndarray:
    """Compute reasonable starting values for the optimizer."""
    var_r = np.var(returns)
    omega_init = np.log(max(var_r * 0.05, 1e-8))
    alpha_init = 0.1
    beta_init = 0.85

    log_rv = np.log(np.clip(rv, 1e-12, None))
    log_var = np.log(max(var_r, 1e-12))
    xi_init = float(np.mean(log_rv) - log_var)
    phi_init = 0.0
    sigma_u_init = np.log(max(np.std(log_rv) * 0.5, 1e-6))

    return np.array([
        omega_init,
        _logit(alpha_init),
        _logit(beta_init),
        xi_init,
        phi_init,
        sigma_u_init,
        0.0,
        0.0,
    ])


def _logit(p: float) -> float:
    return np.log(p / (1.0 - p))


def _neg_log_likelihood(
    theta: np.ndarray,
    returns: np.ndarray,
    rv: np.ndarray,
) -> float:
    """Negative log-likelihood for Realized GARCH (Hansen 2012 eq. 7-8).

    The joint likelihood factors as:
        L = sum_t [log f(r_t | h_t) + log f(log(RV_t) | h_t)]

    Where:
        r_t | h_t ~ N(0, h_t)
        log(RV_t) | h_t ~ N(xi + phi*log(h_t) + tau(z_t), sigma_u^2)
        z_t = r_t / sqrt(h_t)
        tau(z_t) = gamma1*z_t + gamma2*(z_t^2 - 1)
    """
    p = _params_from_vec(theta)
    omega, alpha, beta = p["omega"], p["alpha"], p["beta"]
    xi, phi, sigma_u = p["xi"], p["phi"], p["sigma_u"]
    gamma1, gamma2 = p["gamma1"], p["gamma2"]

    if alpha + beta >= 0.999:
        return 1e10

    n = len(returns)
    h = np.empty(n)
    h[0] = omega / (1.0 - alpha - beta)
    for t in range(1, n):
        h[t] = omega + alpha * returns[t - 1] ** 2 + beta * h[t - 1]
        h[t] = max(h[t], 1e-12)

    z = returns / np.sqrt(h)
    tau = gamma1 * z + gamma2 * (z ** 2 - 1.0)

    log_rv = np.log(np.clip(rv, 1e-12, None))
    mu_rv = xi + phi * np.log(h) + tau
    rv_resid = log_rv - mu_rv

    ll_return = -0.5 * np.sum(np.log(h) + returns ** 2 / h)
    ll_rv = -0.5 * n * np.log(2 * np.pi * sigma_u ** 2) - 0.5 * np.sum(rv_resid ** 2) / sigma_u ** 2

    return -(ll_return + ll_rv)


def fit_realized_garch(
    returns: np.ndarray,
    rv: np.ndarray,
    method: str = "L-BFGS-B",
    max_iter: int = 500,
) -> RealizedGARCHParams:
    """Fit Realized GARCH via MLE.

    Parameters
    ----------
    returns : array (T,)
        Daily log returns.
    rv : array (T,)
        Daily realized variance (same dates as returns).
    method : str
        scipy optimizer method.
    max_iter : int
        Maximum optimizer iterations.

    Returns
    -------
    RealizedGARCHParams with MLE estimates.
    """
    returns = np.asarray(returns, dtype=float)
    rv = np.asarray(rv, dtype=float)
    assert len(returns) == len(rv), f"returns({len(returns)}) != rv({len(rv)})"

    x0 = _initial_params(returns, rv)

    result = minimize(
        _neg_log_likelihood,
        x0,
        args=(returns, rv),
        method=method,
        options={"maxiter": max_iter, "disp": False},
    )

    p = _params_from_vec(result.x)
    return RealizedGARCHParams(
        omega=p["omega"], alpha=p["alpha"], beta=p["beta"],
        xi=p["xi"], phi=p["phi"], sigma_u=p["sigma_u"],
        gamma1=p["gamma1"], gamma2=p["gamma2"],
    )


def realized_garch_forecast(
    params: RealizedGARCHParams,
    returns: np.ndarray,
    rv: np.ndarray,
    horizon: int = 1,
) -> np.ndarray:
    """Compute walk-forward variance forecasts using Realized GARCH.

    For each time step t, the forecast is E[RV_{t+1}] = exp(xi + phi*log(h_t)).
    For multi-step, we iterate: h_{t+k} = omega + alpha*E[eps^2] + beta*h_{t+k-1}
    where E[eps^2_{t+k}] = h_{t+k} (since eps ~ N(0, h)).

    Returns
    -------
    np.ndarray of log-variance forecasts, one per timestep (starting from index 1).
    """
    n = len(returns)
    h = np.empty(n)
    h[0] = params.omega / (1.0 - params.alpha - params.beta + 1e-12)
    for t in range(1, n):
        h[t] = params.omega + params.alpha * returns[t - 1] ** 2 + params.beta * h[t - 1]
        h[t] = max(h[t], 1e-12)

    if horizon == 1:
        rv_pred = np.exp(params.xi + params.phi * np.log(h))
        log_rv_pred = params.xi + params.phi * np.log(h)
        return log_rv_pred

    log_rv_preds = np.full(n, np.nan)
    for t in range(max(1, 0), n):
        h_curr = h[t]
        h_path = []
        for k in range(horizon):
            if k == 0:
                h_next = params.omega + params.alpha * h_curr + params.beta * h_curr
            else:
                h_next = params.omega + (params.alpha + params.beta) * h_path[-1]
            h_next = max(h_next, 1e-12)
            h_path.append(h_next)
        avg_log_h = np.mean([np.log(hk) for hk in h_path])
        log_rv_preds[t] = params.xi + params.phi * avg_log_h

    return log_rv_preds


def realized_garch_log_forecast_at(
    params: RealizedGARCHParams,
    h_t: float,
    horizon: int = 1,
) -> float:
    """Forecast log(RV) at horizon h given current conditional variance h_t.

    Used in walk-forward evaluation where h_t is pre-computed from the
    training sample, and we forecast without peeking at test data.
    """
    if horizon == 1:
        return params.xi + params.phi * np.log(max(h_t, 1e-12))

    h_path = []
    h_curr = h_t
    for k in range(horizon):
        h_next = params.omega + (params.alpha + params.beta) * h_curr
        h_next = max(h_next, 1e-12)
        h_path.append(h_next)
        h_curr = h_next
    avg_log_h = np.mean([np.log(hk) for hk in h_path])
    return params.xi + params.phi * avg_log_h
