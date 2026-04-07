# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class KMeans:
    """Pure numpy K-Means clustering with multi-initialization."""

    def __init__(self, n_clusters=3, n_iter=100, n_init=5):
        self.n_clusters = n_clusters
        self.n_iter = n_iter
        self.n_init = n_init

    def _run_once(self, X, seed):
        rng = np.random.RandomState(seed)
        idx = rng.choice(len(X), self.n_clusters, replace=False)
        centers = X[idx].copy()
        for _ in range(self.n_iter):
            dists = np.linalg.norm(X[:, None] - centers[None], axis=2)
            labels = np.argmin(dists, axis=1)
            new_centers = np.array([
                X[labels == k].mean(axis=0) if (labels == k).sum() > 0
                else centers[k]
                for k in range(self.n_clusters)
            ])
            if np.allclose(centers, new_centers, atol=1e-6):
                break
            centers = new_centers
        inertia = sum(
            np.sum((X[labels == k] - centers[k]) ** 2)
            for k in range(self.n_clusters)
        )
        return labels, centers, inertia

    def fit(self, X):
        best = None
        for seed in range(self.n_init):
            labels, centers, inertia = self._run_once(X, seed)
            if best is None or inertia < best[2]:
                best = (labels, centers, inertia)
        self.labels_ = best[0]
        self.centers_ = best[1]
        return self

    def predict(self, X):
        dists = np.linalg.norm(X[:, None] - self.centers_[None], axis=2)
        return np.argmin(dists, axis=1)


class GaussianHMM:
    """Gaussian HMM with Baum-Welch EM and Viterbi decoding (pure numpy)."""

    def __init__(self, n_states=3, n_iter=60, tol=1e-4):
        self.n_states = n_states
        self.n_iter = n_iter
        self.tol = tol

    def _init_params(self, X):
        T, D = X.shape
        K = self.n_states
        self.pi = np.ones(K) / K
        self.A = np.full((K, K), 0.05 / (K - 1))
        np.fill_diagonal(self.A, 0.95)
        sorted_idx = np.argsort(X[:, 0])
        terciles = np.array_split(sorted_idx, K)
        self.mu = np.array([X[idx].mean(axis=0) for idx in terciles])
        self.sig = np.array([np.var(X, axis=0) + 1e-6] * K)

    def _log_emission(self, X):
        T, D = X.shape
        log_p = np.zeros((T, self.n_states))
        for k in range(self.n_states):
            diff = X - self.mu[k]
            log_det = np.sum(np.log(self.sig[k]))
            mahal = np.sum(diff ** 2 / self.sig[k], axis=1)
            log_p[:, k] = -0.5 * (D * np.log(2 * np.pi) + log_det + mahal)
        return log_p

    def _forward(self, log_emit):
        T, K = log_emit.shape
        log_A = np.log(self.A + 1e-300)
        alpha = np.zeros((T, K))
        alpha[0] = np.log(self.pi + 1e-300) + log_emit[0]
        for t in range(1, T):
            for k in range(K):
                alpha[t, k] = log_emit[t, k] + np.logaddexp.reduce(
                    alpha[t - 1] + log_A[:, k])
        return alpha

    def _backward(self, log_emit):
        T, K = log_emit.shape
        log_A = np.log(self.A + 1e-300)
        beta = np.zeros((T, K))
        for t in range(T - 2, -1, -1):
            for k in range(K):
                beta[t, k] = np.logaddexp.reduce(
                    log_A[k] + log_emit[t + 1] + beta[t + 1])
        return beta

    def fit(self, X):
        self._init_params(X)
        T, D = X.shape
        K = self.n_states
        prev_ll = -np.inf
        for _ in range(self.n_iter):
            log_emit = self._log_emission(X)
            alpha = self._forward(log_emit)
            beta = self._backward(log_emit)
            ll = np.logaddexp.reduce(alpha[-1])
            log_gamma = alpha + beta
            log_gamma -= np.logaddexp.reduce(
                log_gamma, axis=1, keepdims=True)
            gamma = np.exp(log_gamma)
            log_A_mat = np.log(self.A + 1e-300)
            log_xi = np.zeros((T - 1, K, K))
            for t in range(T - 1):
                for i in range(K):
                    for j in range(K):
                        log_xi[t, i, j] = (
                            alpha[t, i] + log_A_mat[i, j]
                            + log_emit[t + 1, j] + beta[t + 1, j]
                        )
                log_xi[t] -= np.logaddexp.reduce(log_xi[t].reshape(-1))
            xi = np.exp(log_xi)
            self.pi = gamma[0] / (gamma[0].sum() + 1e-300)
            self.A = xi.sum(axis=0)
            self.A /= self.A.sum(axis=1, keepdims=True)
            g_sum = gamma.sum(axis=0)
            for k in range(K):
                w = gamma[:, k]
                self.mu[k] = (
                    (w[:, None] * X).sum(axis=0) / (g_sum[k] + 1e-300)
                )
                diff = X - self.mu[k]
                self.sig[k] = (
                    (w[:, None] * diff ** 2).sum(axis=0)
                    / (g_sum[k] + 1e-300) + 1e-6
                )
            if abs(ll - prev_ll) < self.tol:
                break
            prev_ll = ll
        self.log_likelihood_ = ll
        return self

    def predict(self, X):
        T, D = X.shape
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


ALLOC = {
    "bull": (0.85, 0.05, 0.00, 0.10, 0.00),
    "neutral": (0.45, 0.30, 0.10, 0.15, 0.00),
    "bear": (0.05, 0.35, 0.20, 0.20, 0.20),
}

CRISIS_VOL_THRESHOLD = 0.25


class HMMKMeansVoting(QCAlgorithm):
    """
    HMM + K-Means Voting Regime Detection
    ======================================
    Dual-model ensemble: HMM (Baum-Welch) + K-Means vote on market regime.
    Crisis circuit breaker: 5d vol > 25% -> force bear.
    Features: returns, vol20, mom60, vol_ratio (MAD winsorized).
    Universe: SPY, TLT, IEF, GLD, DJP

    Source: ECE student project (Brusset, Gr01 H.4), adapted for ESGF pool.
    Issue #238 - Integrate ECE student concepts into QC strategies.
    """

    def initialize(self):
        self.set_start_date(2010, 1, 1)
        self.set_end_date(2024, 1, 1)
        self.set_cash(100_000)
        self.set_brokerage_model(
            BrokerageName.INTERACTIVE_BROKERS_BROKERAGE,
            AccountType.MARGIN
        )
        self.set_benchmark("SPY")

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.tlt = self.add_equity("TLT", Resolution.DAILY).symbol
        self.ief = self.add_equity("IEF", Resolution.DAILY).symbol
        self.gld = self.add_equity("GLD", Resolution.DAILY).symbol
        self.djp = self.add_equity("DJP", Resolution.DAILY).symbol

        self.set_warm_up(300, Resolution.DAILY)

        self.hmm = None
        self.kmeans = None
        self.regime = None
        self._mu_scale = None
        self._std_scale = None
        self._crisis_active = False

        self.schedule.on(
            self.date_rules.month_start(self.spy),
            self.time_rules.after_market_open(self.spy, 30),
            self._monthly_rebalance
        )
        self.schedule.on(
            self.date_rules.every_day(self.spy),
            self.time_rules.after_market_open(self.spy, 60),
            self._daily_crisis_check
        )

    def _get_features(self, lookback=400):
        bars = self.history(self.spy, lookback + 10, Resolution.DAILY)
        if bars is None or bars.empty or len(bars) < 80:
            return None, None, None

        close = bars["close"].values.astype(float)
        ret = np.diff(np.log(close + 1e-10))
        n = len(ret)

        vol20 = np.array([ret[max(0, i - 19):i + 1].std() for i in range(n)])
        vol60 = np.array([ret[max(0, i - 59):i + 1].std() for i in range(n)])
        mom60 = np.array([
            (close[i + 1] / close[max(0, i - 58)] - 1) for i in range(n)
        ])
        vol_ratio = vol20 / (vol60 + 1e-9)

        start = 60
        X_raw = np.column_stack([
            ret[start:], vol20[start:], mom60[start:], vol_ratio[start:]
        ])

        if len(X_raw) < 40:
            return None, None, None

        for col in range(X_raw.shape[1]):
            m = np.median(X_raw[:, col])
            mad = np.median(np.abs(X_raw[:, col] - m)) * 1.4826
            X_raw[:, col] = np.clip(X_raw[:, col], m - 4 * mad, m + 4 * mad)

        mu = X_raw.mean(axis=0)
        std = X_raw.std(axis=0) + 1e-9
        X = (X_raw - mu) / std
        return X, mu, std

    def _label_states(self, X, states):
        mean_vol, mean_ret = {}, {}
        for k in np.unique(states):
            mask = (states == k)
            mean_vol[k] = X[mask, 1].mean() if mask.sum() > 0 else 0.0
            mean_ret[k] = X[mask, 0].mean() if mask.sum() > 0 else 0.0
        bear_k = max(mean_vol, key=mean_vol.get)
        remaining = [k for k in mean_vol if k != bear_k]
        bull_k = max(remaining, key=lambda k: mean_ret[k])
        neutral_k = [k for k in remaining if k != bull_k][0]
        return {bear_k: "bear", neutral_k: "neutral", bull_k: "bull"}

    def _train_models(self):
        X, mu, std = self._get_features(lookback=400)
        if X is None:
            return False

        min_obs = max(8, int(len(X) * 0.02))

        hmm = GaussianHMM(n_states=3, n_iter=60, tol=1e-4)
        try:
            hmm.fit(X)
        except Exception as e:
            self.debug(f"HMM error: {e}")
            return False
        hmm_states = hmm.predict(X)
        for k in range(3):
            if (hmm_states == k).sum() < min_obs:
                return False
        hmm.regime_map = self._label_states(X, hmm_states)

        km = KMeans(n_clusters=3, n_iter=100, n_init=5)
        try:
            km.fit(X)
        except Exception as e:
            self.debug(f"KMeans error: {e}")
            return False
        km_states = km.labels_
        for k in range(3):
            if (km_states == k).sum() < min_obs:
                return False
        km.regime_map = self._label_states(X, km_states)

        self.hmm = hmm
        self.kmeans = km
        self._mu_scale = mu
        self._std_scale = std
        return True

    def _detect_regime(self):
        if self.hmm is None or self.kmeans is None:
            return None

        bars = self.history(self.spy, 30, Resolution.DAILY)
        if bars is None or bars.empty or len(bars) < 25:
            return None

        close = bars["close"].values.astype(float)
        ret = np.diff(np.log(close + 1e-10))
        n = len(ret)
        vol20 = np.array([ret[max(0, i - 19):i + 1].std() for i in range(n)])
        vol60 = np.array([ret[max(0, i - 59):i + 1].std() for i in range(n)])
        mom60 = np.array([
            (close[i + 1] / close[max(0, i - 58)] - 1) for i in range(n)
        ])
        vol_ratio = vol20 / (vol60 + 1e-9)
        X_raw = np.column_stack([ret, vol20, mom60, vol_ratio])

        for col in range(X_raw.shape[1]):
            m = np.median(X_raw[:, col])
            mad = np.median(np.abs(X_raw[:, col] - m)) * 1.4826
            X_raw[:, col] = np.clip(X_raw[:, col], m - 4 * mad, m + 4 * mad)

        X = (X_raw - self._mu_scale) / self._std_scale

        hmm_regime = self.hmm.regime_map.get(
            self.hmm.predict(X)[-1], "neutral"
        )
        km_regime = self.kmeans.regime_map.get(
            self.kmeans.predict(X)[-1], "neutral"
        )

        if hmm_regime == km_regime:
            final = hmm_regime
        else:
            priority = {"bear": 0, "neutral": 1, "bull": 2}
            final = min(hmm_regime, km_regime, key=lambda r: priority[r])

        self.debug(
            f"{self.time.date()} | HMM={hmm_regime} KM={km_regime}"
            f" -> {final.upper()}"
        )
        return final

    def _daily_crisis_check(self):
        if self.is_warming_up:
            return

        bars = self.history(self.spy, 7, Resolution.DAILY)
        if bars is None or bars.empty or len(bars) < 6:
            return

        close = bars["close"].values.astype(float)
        vol5 = np.diff(np.log(close + 1e-10))[-5:].std() * np.sqrt(252)

        if vol5 > CRISIS_VOL_THRESHOLD and not self._crisis_active:
            self._crisis_active = True
            self.regime = "bear"
            spy_w, tlt_w, ief_w, gld_w, djp_w = ALLOC["bear"]
            self.debug(
                f"{self.time.date()} | CRISIS vol5={vol5:.1%} -> bear forced"
            )
            self.liquidate()
            self.set_holdings(self.spy, spy_w)
            self.set_holdings(self.tlt, tlt_w)
            self.set_holdings(self.ief, ief_w)
            self.set_holdings(self.gld, gld_w)
            self.set_holdings(self.djp, djp_w)

        elif vol5 <= CRISIS_VOL_THRESHOLD and self._crisis_active:
            self._crisis_active = False
            self.debug(
                f"{self.time.date()} | Crisis ended vol5={vol5:.1%}"
            )
            self._monthly_rebalance()

    def _monthly_rebalance(self):
        if self.is_warming_up or self._crisis_active:
            return

        if not self._train_models():
            self.debug("Models unavailable - allocation unchanged")
            return

        regime = self._detect_regime()
        if regime is None:
            return

        self.regime = regime
        spy_w, tlt_w, ief_w, gld_w, djp_w = ALLOC[regime]

        self.debug(
            f"{self.time.date()} | {regime.upper()} | "
            f"SPY={spy_w:.0%} TLT={tlt_w:.0%} IEF={ief_w:.0%} "
            f"GLD={gld_w:.0%} DJP={djp_w:.0%}"
        )

        self.liquidate()
        self.set_holdings(self.spy, spy_w)
        self.set_holdings(self.tlt, tlt_w)
        self.set_holdings(self.ief, ief_w)
        self.set_holdings(self.gld, gld_w)
        self.set_holdings(self.djp, djp_w)

    def on_data(self, data: Slice):
        if self.is_warming_up:
            return
        if not self.portfolio.invested:
            self._monthly_rebalance()
