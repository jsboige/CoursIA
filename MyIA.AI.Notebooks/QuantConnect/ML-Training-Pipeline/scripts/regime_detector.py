"""
Regime detection for financial time series — shared module.

Provides two complementary approaches:
1. Price-based regime classification (rolling return + volatility + drawdown)
2. HMM-based regime detection (Gaussian HMM with Baum-Welch EM)

Used by:
- MoE routing: route to expert NN per regime (Issue #754 Phase B)
- FinTSB-style per-regime evaluation (eval_finstsb.py)
- Walk-forward training with regime-aware splitting

References:
- Hamilton (1989), "A New Approach to the Economic Analysis of Nonstationary
  Time Series and the Business Cycle"
- Almgren & Chriss (2001), optimal execution under regime uncertainty
- Hands-On AI Trading, Pik et al., Wiley 2025 — regime-aware strategies
"""

from __future__ import annotations

import numpy as np
import pandas as pd
from dataclasses import dataclass


# ---------------------------------------------------------------------------
# Price-based regime detection (from eval_finstsb.py, made standalone)
# ---------------------------------------------------------------------------

def detect_regimes_price(
    prices: pd.Series | np.ndarray,
    lookback_days: int = 60,
    uptrend_threshold: float = 0.10,
    downtrend_threshold: float = -0.10,
    volatility_percentile: float = 75,
    black_swan_drawdown: float = -0.20,
    black_swan_window: int = 30,
) -> pd.Series:
    """Classify each date into a market regime using price statistics.

    Regimes: "uptrend", "downtrend", "volatility", "black_swan".

    Parameters
    ----------
    prices : array-like
        Daily price series.
    lookback_days : int
        Rolling window for regime detection.
    uptrend_threshold : float
        Minimum rolling return to classify as uptrend.
    downtrend_threshold : float
        Maximum rolling return to classify as downtrend.
    volatility_percentile : float
        Percentile threshold for high-volatility regime (0-100).
    black_swan_drawdown : float
        Drawdown threshold for black swan (e.g. -0.20 = -20%).
    black_swan_window : int
        Window for drawdown calculation.

    Returns
    -------
    pd.Series of regime labels aligned to prices index.
    """
    prices = pd.Series(prices).reset_index(drop=True)
    returns = prices.pct_change()

    rolling_return = prices.pct_change(lookback_days)
    rolling_std = returns.rolling(lookback_days).std() * np.sqrt(252)
    vol_threshold = rolling_std.quantile(volatility_percentile / 100)

    rolling_max = prices.rolling(black_swan_window, min_periods=1).max()
    drawdown = (prices - rolling_max) / rolling_max

    regimes = pd.Series("normal", index=prices.index, dtype="object")

    # Priority order: black_swan > uptrend > downtrend > volatility
    regimes[drawdown <= black_swan_drawdown] = "black_swan"

    mask_up = (rolling_return >= uptrend_threshold) & (regimes == "normal")
    regimes[mask_up] = "uptrend"

    mask_down = (rolling_return <= downtrend_threshold) & (regimes == "normal")
    regimes[mask_down] = "downtrend"

    mask_vol = (rolling_std >= vol_threshold) & (regimes == "normal")
    regimes[mask_vol] = "volatility"

    # Remaining "normal" -> mild uptrend or downtrend
    normal_mask = regimes == "normal"
    regimes[normal_mask & (rolling_return > 0)] = "uptrend"
    regimes[normal_mask & (rolling_return <= 0)] = "downtrend"

    # Fill NaN from rolling calculations
    regimes = regimes.fillna("normal")
    # Replace remaining "normal" after fill
    regimes[regimes == "normal"] = "uptrend"

    return regimes


# ---------------------------------------------------------------------------
# HMM-based regime detection (from HMM-KMeans-Voting, standalone)
# ---------------------------------------------------------------------------

@dataclass
class HMMRegimeResult:
    """Result from HMM regime detection."""
    labels: np.ndarray          # Integer state labels (0, 1, ..., n_states-1)
    regime_names: list[str]     # Human-readable regime names per state
    log_likelihood: float       # Final log-likelihood
    n_states: int               # Number of HMM states
    transition_matrix: np.ndarray  # State transition probabilities


class GaussianHMM:
    """Gaussian HMM with Baum-Welch EM and Viterbi decoding (pure numpy).

    Suitable for financial regime detection where observations are
    continuous (returns, volatility, momentum, etc.).

    Parameters
    ----------
    n_states : int
        Number of hidden states (regimes). Default 3 (bull/bear/neutral).
    n_iter : int
        Maximum EM iterations.
    tol : float
        Convergence tolerance for log-likelihood.
    """

    def __init__(self, n_states: int = 3, n_iter: int = 60, tol: float = 1e-4):
        self.n_states = n_states
        self.n_iter = n_iter
        self.tol = tol

    def _init_params(self, X: np.ndarray) -> None:
        T, D = X.shape
        K = self.n_states
        self.pi = np.ones(K) / K
        self.A = np.full((K, K), 0.05 / (K - 1))
        np.fill_diagonal(self.A, 0.95)
        sorted_idx = np.argsort(X[:, 0])
        terciles = np.array_split(sorted_idx, K)
        self.mu = np.array([X[idx].mean(axis=0) for idx in terciles])
        self.sig = np.array([np.var(X, axis=0) + 1e-6] * K)

    def _log_emission(self, X: np.ndarray) -> np.ndarray:
        T, D = X.shape
        log_p = np.zeros((T, self.n_states))
        for k in range(self.n_states):
            diff = X - self.mu[k]
            log_det = np.sum(np.log(self.sig[k]))
            mahal = np.sum(diff ** 2 / self.sig[k], axis=1)
            log_p[:, k] = -0.5 * (D * np.log(2 * np.pi) + log_det + mahal)
        return log_p

    def _forward(self, log_emit: np.ndarray) -> np.ndarray:
        T, K = log_emit.shape
        log_A = np.log(self.A + 1e-300)
        alpha = np.zeros((T, K))
        alpha[0] = np.log(self.pi + 1e-300) + log_emit[0]
        for t in range(1, T):
            for k in range(K):
                alpha[t, k] = log_emit[t, k] + np.logaddexp.reduce(
                    alpha[t - 1] + log_A[:, k]
                )
        return alpha

    def _backward(self, log_emit: np.ndarray) -> np.ndarray:
        T, K = log_emit.shape
        log_A = np.log(self.A + 1e-300)
        beta = np.zeros((T, K))
        for t in range(T - 2, -1, -1):
            for k in range(K):
                beta[t, k] = np.logaddexp.reduce(
                    log_A[k] + log_emit[t + 1] + beta[t + 1]
                )
        return beta

    def fit(self, X: np.ndarray) -> GaussianHMM:
        """Fit HMM parameters via Baum-Welch EM.

        Parameters
        ----------
        X : np.ndarray, shape (T, D)
            Observation matrix (T timesteps, D features).

        Returns
        -------
        self
        """
        self._init_params(X)
        prev_ll = -np.inf
        K = self.n_states

        for _ in range(self.n_iter):
            log_emit = self._log_emission(X)
            alpha = self._forward(log_emit)
            beta = self._backward(log_emit)
            ll = np.logaddexp.reduce(alpha[-1])

            log_gamma = alpha + beta
            log_gamma -= np.logaddexp.reduce(log_gamma, axis=1, keepdims=True)
            gamma = np.exp(log_gamma)

            log_A_mat = np.log(self.A + 1e-300)
            log_xi = np.zeros((len(X) - 1, K, K))
            for t in range(len(X) - 1):
                for i in range(K):
                    for j in range(K):
                        log_xi[t, i, j] = (
                            alpha[t, i]
                            + log_A_mat[i, j]
                            + log_emit[t + 1, j]
                            + beta[t + 1, j]
                        )
                log_xi[t] -= np.logaddexp.reduce(log_xi[t].reshape(-1))
            xi = np.exp(log_xi)

            self.pi = gamma[0] / (gamma[0].sum() + 1e-300)
            self.A = xi.sum(axis=0)
            self.A /= self.A.sum(axis=1, keepdims=True)

            g_sum = gamma.sum(axis=0)
            for k in range(K):
                w = gamma[:, k]
                self.mu[k] = (w[:, None] * X).sum(axis=0) / (g_sum[k] + 1e-300)
                diff = X - self.mu[k]
                self.sig[k] = (
                    (w[:, None] * diff ** 2).sum(axis=0)
                    / (g_sum[k] + 1e-300)
                    + 1e-6
                )

            if abs(ll - prev_ll) < self.tol:
                break
            prev_ll = ll

        self.log_likelihood_ = ll
        return self

    def predict(self, X: np.ndarray) -> np.ndarray:
        """Decode most likely state sequence via Viterbi.

        Parameters
        ----------
        X : np.ndarray, shape (T, D)
            Observation matrix.

        Returns
        -------
        np.ndarray of int, shape (T,)
            Most likely state sequence.
        """
        T = len(X)
        K = self.n_states
        log_A = np.log(self.A + 1e-300)
        log_emit = self._log_emission(X)

        viterbi = np.zeros((T, K))
        backptr = np.zeros((T, K), dtype=int)
        viterbi[0] = np.log(self.pi + 1e-300) + log_emit[0]

        for t in range(1, T):
            for k in range(K):
                scores = viterbi[t - 1] + log_A[:, k]
                backptr[t, k] = np.argmax(scores)
                viterbi[t, k] = scores[backptr[t, k]] + log_emit[t, k]

        states = np.zeros(T, dtype=int)
        states[-1] = np.argmax(viterbi[-1])
        for t in range(T - 2, -1, -1):
            states[t] = backptr[t + 1, states[t + 1]]
        return states


def detect_regimes_hmm(
    prices: pd.Series | np.ndarray,
    n_states: int = 3,
    lookback: int = 400,
    min_samples: int = 80,
) -> HMMRegimeResult:
    """Detect market regimes using Gaussian HMM on price features.

    Features computed from prices:
    - Daily log returns
    - 20-day rolling volatility
    - 60-day momentum
    - Volatility ratio (20d / 60d)

    State naming convention (based on mean return):
    - Highest mean return -> "bull"
    - Lowest mean return -> "bear"
    - Middle -> "neutral"

    Parameters
    ----------
    prices : array-like
        Daily price series.
    n_states : int
        Number of HMM states (default 3: bull/neutral/bear).
    lookback : int
        Maximum history to use for feature computation.
    min_samples : int
        Minimum samples required for fitting.

    Returns
    -------
    HMMRegimeResult with labels, regime_names, and metadata.
    """
    original_prices = pd.Series(prices).reset_index(drop=True)
    original_len = len(original_prices)

    prices = original_prices.iloc[-lookback:] if original_len > lookback else original_prices
    offset = original_len - len(prices)

    close = prices.values.astype(float)
    ret = np.diff(np.log(close + 1e-10))
    n = len(ret)

    if n < min_samples:
        return HMMRegimeResult(
            labels=np.zeros(original_len, dtype=int),
            regime_names=["unknown"] * n_states,
            log_likelihood=0.0,
            n_states=n_states,
            transition_matrix=np.eye(n_states),
        )

    vol20 = np.array([ret[max(0, i - 19):i + 1].std() for i in range(n)])
    vol60 = np.array([ret[max(0, i - 59):i + 1].std() for i in range(n)])
    mom60 = np.array([(close[i + 1] / close[max(0, i - 58)] - 1) for i in range(n)])
    vol_ratio = vol20 / (vol60 + 1e-9)

    start = 60
    X_raw = np.column_stack([ret[start:], vol20[start:], mom60[start:], vol_ratio[start:]])

    # MAD winsorization
    for col in range(X_raw.shape[1]):
        m = np.median(X_raw[:, col])
        mad = np.median(np.abs(X_raw[:, col] - m)) * 1.4826
        X_raw[:, col] = np.clip(X_raw[:, col], m - 4 * mad, m + 4 * mad)

    hmm = GaussianHMM(n_states=n_states)
    hmm.fit(X_raw)
    labels_raw = hmm.predict(X_raw)

    # Name states by mean return (column 0)
    state_means = []
    for k in range(n_states):
        mask = labels_raw == k
        if mask.sum() > 0:
            state_means.append((k, X_raw[mask, 0].mean()))
        else:
            state_means.append((k, 0.0))

    sorted_states = sorted(state_means, key=lambda x: x[1], reverse=True)
    state_names = ["unknown"] * n_states
    if n_states >= 3:
        state_names[sorted_states[0][0]] = "bull"
        state_names[sorted_states[-1][0]] = "bear"
        for i in range(1, n_states - 1):
            state_names[sorted_states[i][0]] = "neutral"
    elif n_states == 2:
        state_names[sorted_states[0][0]] = "bull"
        state_names[sorted_states[-1][0]] = "bear"

    # Map labels to original price series length
    full_labels = np.zeros(original_len, dtype=int)
    full_labels[offset + start + 1:] = labels_raw

    return HMMRegimeResult(
        labels=full_labels,
        regime_names=state_names,
        log_likelihood=hmm.log_likelihood_,
        n_states=n_states,
        transition_matrix=hmm.A.copy(),
    )


# ---------------------------------------------------------------------------
# Convenience: combined regime detection
# ---------------------------------------------------------------------------

def detect_regimes(
    prices: pd.Series | np.ndarray,
    method: str = "price",
    **kwargs,
) -> pd.Series:
    """Detect market regimes using specified method.

    Parameters
    ----------
    prices : array-like
        Daily price series.
    method : str
        "price" for price-based (fast, deterministic) or
        "hmm" for HMM-based (slower, probabilistic).
    **kwargs
        Additional arguments passed to the underlying detector.

    Returns
    -------
    pd.Series of regime labels (string).
    """
    if method == "price":
        return detect_regimes_price(prices, **kwargs)
    elif method == "hmm":
        result = detect_regimes_hmm(prices, **kwargs)
        labels = result.labels
        names = result.regime_names
        return pd.Series(
            [names[l] for l in labels],
            index=pd.Series(prices).index,
            dtype="object",
        )
    else:
        raise ValueError(f"Unknown method: {method}. Use 'price' or 'hmm'.")
