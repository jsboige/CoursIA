# region imports
from AlgorithmImports import *
from itertools import combinations

import numpy as np
from scipy.optimize import nnls
# endregion

# ===========================================================================
# Sparse Index Tracking under a cardinality constraint -- QC Cloud edition
# ===========================================================================
# Real-data companion of App-27 (Search/Applications/Hybrid/
# App-27-Sparse-Index-Tracking-Walk-Forward.ipynb, PR #14046).
# App-27 carries the METHOD on synthetic data with known truth (CP-SAT model,
# independent validator, walk-forward protocol, leak counter-example);
# this project carries the TEST AGAINST REAL DATA via a real QC Cloud
# backtest with explicit transaction costs.
#
# Engine distinction (documented honestly, issue #14062):
#   - App-27 solves the cardinality problem with OR-Tools CP-SAT over integer
#     lots: exact optimizer with status/bound/gap (sector caps + turnover
#     constraint native).
#   - This QC implementation deliberately uses an EXACT ENUMERATION over a
#     correlation-ranked shortlist with SciPy NNLS, keeping the cloud algorithm
#     bounded and directly reproducible. Every K-subset of the shortlist is
#     solved exactly (NNLS),
#     so the selection is provably optimal WITHIN the shortlist; the
#     shortlist ranking itself is a heuristic filter (correlation with the
#     benchmark on the calibration window). No sector cap, no turnover
#     constraint (a no-trade band controls turnover instead).
#
# Protocol (walk-forward, mirrors App-27 section 5):
#   - Quarterly rebalance (63 trading days).
#   - At each rebalance date t: calibration window = the 252 daily returns
#     ending 63 trading days before t; validation window = the 63 returns
#     (t-63, t); the traded quarter (t, t+63] is the OOS test block, never
#     used for selection.
#   - Sparse mode: universe ranked by correlation with SPY on the
#     calibration window only; for each candidate K in {6, 8, 10} every
#     K-subset of the 12-asset shortlist is enumerated (NNLS on calibration,
#     exactly K positive weights enforced); K is chosen on the VALIDATION
#     window; final weights re-solved on calibration+validation.
#   - Full mode (baseline): NNLS over all 40 assets on calibration+validation,
#     no cardinality constraint.
#   - Independent validator (App-27 section 4): budget, cardinality <= K and
#     minimum weight are re-checked from the final weight vector alone.
#
# Costs: explicit 5 bps per trade on notional via PercentFeeModel (canonical
# repo pattern, cf Portfolio-IBKR-Coinbase-Hybrid/main.py). A sparse
# selection exists precisely to save on costs: omitting them would hollow
# out the demonstration (issue #14062 acceptance #3). No slippage model:
# the fee effect is isolated on purpose.
# ===========================================================================

BENCHMARK = "SPY"

# 40 US mega/large caps, all continuously listed 2015-2026. Fixed universe:
# no QC Universe Selection (repo rule), and no survivorship-free selection
# process -- chosen in 2026, hence survivorship-biased toward winners.
# Documented limitation, see README.
UNIVERSE = [
    "MSFT", "AAPL", "NVDA", "AMZN", "META", "GOOGL", "TSLA", "AVGO",
    "JPM", "V", "MA", "UNH", "JNJ", "WMT", "PG", "KO",
    "PEP", "HD", "MRK", "PFE", "ABBV", "XOM", "CVX", "CAT",
    "MMM", "BA", "DIS", "MCD", "COST", "INTC", "CSCO", "ORCL",
    "IBM", "GE", "T", "VZ", "ADBE", "CRM", "TXN", "QCOM",
]

CANDIDATE_K = (6, 8, 10)
SHORTLIST_SIZE = 12
CALIBRATION_DAYS = 252   # one year of daily returns
VALIDATION_DAYS = 63     # one quarter of daily returns
REBALANCE_DAYS = 63      # quarterly rebalance
NO_TRADE_BAND = 0.10     # skip rebalance below 10% one-way turnover
MIN_WEIGHT = 0.01        # dust filter: drop weights < 1%, renormalize
TOTAL_BARS = CALIBRATION_DAYS + VALIDATION_DAYS + 1


class PercentFeeModel(FeeModel):
    """Charges a fixed percent of the order notional value as commission.

    Canonical repo pattern (cf Portfolio-IBKR-Coinbase-Hybrid/main.py).
    5 bps of notional per trade, both modes, so the sparse-vs-full
    comparison is run under identical explicit costs.
    """

    def __init__(self, percent):
        super().__init__()
        self.percent = percent

    def get_order_fee(self, parameters):
        security = parameters.security
        order = parameters.order
        notional = abs(order.quantity) * float(security.price)
        return OrderFee(CashAmount(self.percent * notional, security.quote_currency.symbol))


def solve_tracking_weights(asset_returns, benchmark_returns):
    """Non-negative least squares tracking of the benchmark.

    Minimizes ||asset_returns @ w - benchmark_returns||^2 with w >= 0
    (scipy.optimize.nnls), then normalizes w to sum to 1 -- the portfolio
    actually traded is fully invested, so the RMSE is computed on the
    NORMALIZED weights (honest about what we trade).

    Returns (weights, rmse); rmse is +inf when no positive weight exists.
    """
    n_assets = asset_returns.shape[1]
    if n_assets == 0:
        return np.zeros(0), float("inf")
    weights, _ = nnls(asset_returns, benchmark_returns)
    total = weights.sum()
    if total <= 0.0:
        return np.zeros(n_assets), float("inf")
    weights = weights / total
    active = asset_returns @ weights - benchmark_returns
    rmse = float(np.sqrt(np.mean(active ** 2)))
    return weights, rmse


def active_rmse(asset_returns, benchmark_returns, weights):
    """Post-normalization active RMSE of an already-normalized weight vector."""
    active = asset_returns @ weights - benchmark_returns
    return float(np.sqrt(np.mean(active ** 2)))


def rank_shortlist(X_cal, y_cal, shortlist_size):
    """Rank assets by correlation with the benchmark on the CALIBRATION
    window only (no future data), keep the top `shortlist_size`."""
    n_assets = X_cal.shape[1]
    correlations = np.array(
        [np.corrcoef(X_cal[:, i], y_cal)[0, 1] for i in range(n_assets)]
    )
    correlations = np.nan_to_num(correlations, nan=-1.0)
    return np.argsort(correlations)[-shortlist_size:], correlations


def select_sparse_portfolio(X_cal, y_cal, X_val, y_val, X_full, y_full,
                            candidate_k=CANDIDATE_K, shortlist_size=SHORTLIST_SIZE):
    """Exact-within-shortlist sparse selection with validation-chosen K.

    For each candidate K: enumerate every K-subset of the correlation
    shortlist, solve NNLS on the calibration window, keep the subset with
    the lowest post-normalization calibration RMSE among those using
    EXACTLY K positive weights (subsets whose NNLS zeroes an asset are
    rejected -- effective cardinality < K violates the constraint).
    K is then chosen on the validation window, and the final weights are
    re-solved on calibration+validation with the selected assets.

    Returns dict | None (None = no feasible combination, caller keeps the
    previous portfolio).
    """
    shortlist, correlations = rank_shortlist(X_cal, y_cal, shortlist_size)
    per_k = {}
    for k in candidate_k:
        best = None
        for combo in combinations(shortlist.tolist(), k):
            idx = np.array(combo, dtype=int)
            weights, cal_rmse = solve_tracking_weights(X_cal[:, idx], y_cal)
            if not np.isfinite(cal_rmse):
                continue
            if np.any(weights <= 1e-8):
                continue  # NNLS zeroed an asset: effective cardinality < k
            if best is None or cal_rmse < best[0]:
                best = (cal_rmse, idx, weights)
        if best is None:
            continue
        cal_rmse, idx, cal_weights = best
        val_rmse = active_rmse(X_val[:, idx], y_val, cal_weights)
        per_k[k] = {
            "cal_rmse": cal_rmse,
            "val_rmse": val_rmse,
            "assets_idx": idx,
        }
    if not per_k:
        return None
    chosen_k = min(per_k, key=lambda k: per_k[k]["val_rmse"])
    idx = per_k[chosen_k]["assets_idx"]
    final_weights, full_rmse = solve_tracking_weights(X_full[:, idx], y_full)
    if not np.isfinite(full_rmse):
        return None
    return {
        "chosen_k": chosen_k,
        "assets_idx": idx,
        "weights": final_weights,
        "cal_rmse": per_k[chosen_k]["cal_rmse"],
        "val_rmse": per_k[chosen_k]["val_rmse"],
        "full_rmse": full_rmse,
        "shortlist": shortlist,
        "correlations": correlations,
    }


def validate_weights(weights, k_expected=None, min_weight=MIN_WEIGHT):
    """Independent feasibility validator (App-27 section 4 spirit).

    Re-checks the constraints from the final weight vector alone, without
    consulting the solver. Called after every weight construction.
    """
    positive = weights > 1e-8
    checks = {
        "budget_ok": bool(abs(float(weights.sum()) - 1.0) < 1e-6),
        "n_positive": int(positive.sum()),
        "min_weight_ok": bool(np.all(weights[positive] >= min_weight - 1e-9)),
    }
    if k_expected is not None:
        # Selection enforces exactly K on calibration; after the full-window
        # re-solve and dust filter the traded portfolio may only use FEWER.
        checks["cardinality_ok"] = bool(checks["n_positive"] <= k_expected)
    return checks


class SparseIndexTrackingAlgorithm(QCAlgorithm):
    """Sparse index tracking vs full replication, SPY benchmark.

    Parameters (QC backtest API):
      mode       : "sparse" (cardinality-constrained) | "full" (baseline)
      fee_bps    : explicit fee in basis points of notional (default 5)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 8, 31)
        self.set_cash(100000)

        self.mode = self.get_parameter("mode", "sparse").lower()
        if self.mode not in ("sparse", "full"):
            raise ValueError(f"unknown mode '{self.mode}' (expected sparse|full)")
        self.fee_bps = float(self.get_parameter("fee_bps", 5.0))

        self.set_security_initializer(self._security_initializer)

        self.spy_symbol = self.add_equity(BENCHMARK, Resolution.DAILY).symbol
        self.asset_symbols = [
            self.add_equity(ticker, Resolution.DAILY).symbol for ticker in UNIVERSE
        ]
        self.all_symbols = [self.spy_symbol] + self.asset_symbols

        self.set_benchmark(BENCHMARK)
        self.set_warm_up(TOTAL_BARS, Resolution.DAILY)

        self._day_count = 0
        self._has_positions = False
        self._rebalances = 0
        self._skipped = 0
        self._total_turnover = 0.0

    def _security_initializer(self, security):
        security.set_fee_model(PercentFeeModel(self.fee_bps / 10000.0))

    def on_data(self, data):
        if self.is_warming_up:
            return
        self._day_count += 1
        if self._day_count % REBALANCE_DAYS != 1:
            return
        self._rebalance()

    def _get_returns(self):
        """Return (X, y, asset_symbols): last 315 daily returns, SPY last.

        Assets with missing data in the window are dropped (no forward-fill
        gambling); the frame is defensive about pandas level ordering.
        """
        hist = self.history(self.all_symbols, TOTAL_BARS, Resolution.DAILY)
        close = hist["close"].unstack(level=0)
        if len(close.index) > 0 and not hasattr(close.index[0], "date"):
            # level 0 carried timestamps (lean index ordering varies) -> swap
            close = hist["close"].unstack(level=1)
        close = close.dropna(axis=1)
        if close.shape[0] < TOTAL_BARS:
            return None
        returns = close.pct_change().dropna(axis=0)
        returns = returns.iloc[-(CALIBRATION_DAYS + VALIDATION_DAYS):]

        spy_cols = [c for c in returns.columns if c.value == BENCHMARK]
        if not spy_cols:
            return None
        spy_col = spy_cols[0]
        asset_cols = [c for c in returns.columns if c != spy_col]
        if len(asset_cols) < 8:
            return None
        y = returns[spy_col].to_numpy(dtype=float)
        X = returns[asset_cols].to_numpy(dtype=float)
        return X, y, asset_cols

    def _current_weights(self, equity):
        out = {}
        for symbol in self.asset_symbols:
            holdings = self.portfolio[symbol]
            if holdings.invested and equity > 0:
                out[symbol] = holdings.holdings_value / equity
        return out

    def _rebalance(self):
        data = self._get_returns()
        if data is None:
            self.debug(f"[{self.mode}] insufficient history at {self.time}, postponing")
            return
        X, y, asset_cols = data
        split = CALIBRATION_DAYS
        X_cal, y_cal = X[:split], y[:split]
        X_val, y_val = X[split:], y[split:]

        if self.mode == "sparse":
            selection = select_sparse_portfolio(X_cal, y_cal, X_val, y_val, X, y)
            if selection is None:
                self.debug(f"[{self.mode}] no feasible K-subset at {self.time}, keeping portfolio")
                self._skipped += 1
                return
            idx = selection["assets_idx"]
            raw_weights = selection["weights"]
            k_expected = selection["chosen_k"]
        else:
            raw_weights, cal_rmse = solve_tracking_weights(X, y)
            if not np.isfinite(cal_rmse):
                self.debug(f"[{self.mode}] NNLS infeasible at {self.time}, keeping portfolio")
                self._skipped += 1
                return
            idx = np.arange(X.shape[1])
            k_expected = None
            selection = {"chosen_k": len(idx), "cal_rmse": cal_rmse,
                         "val_rmse": float("nan"), "full_rmse": cal_rmse}

        # Dust filter: drop sub-1% weights, renormalize.
        keep = raw_weights >= MIN_WEIGHT
        if keep.sum() == 0:
            self._skipped += 1
            return
        weights = raw_weights[keep] / raw_weights[keep].sum()
        kept_idx = idx[keep]

        checks = validate_weights(weights, k_expected=k_expected)
        if not (checks["budget_ok"] and checks["min_weight_ok"]
                and checks.get("cardinality_ok", True)):
            self.debug(f"[{self.mode}] validator FAILED at {self.time}: {checks}, keeping portfolio")
            self._skipped += 1
            return

        targets = {}
        for local_i, asset_i in enumerate(kept_idx):
            targets[asset_cols[asset_i]] = float(weights[local_i])

        equity = self.portfolio.total_portfolio_value
        current = self._current_weights(equity)
        turnover = 0.5 * sum(
            abs(targets.get(s, 0.0) - current.get(s, 0.0)) for s in set(targets) | set(current)
        )
        if self._has_positions and turnover < NO_TRADE_BAND:
            self._skipped += 1
            self.debug(
                f"[{self.mode}] {self.time:%Y-%m-%d} skip: turnover {turnover:.1%} < {NO_TRADE_BAND:.0%}"
            )
            return

        self.set_holdings(
            [PortfolioTarget(symbol, weight) for symbol, weight in targets.items()],
            True,
        )
        self._rebalances += 1
        self._has_positions = True
        self._total_turnover += turnover
        self.plot("Selection", "Cardinality (assets held)", int(len(targets)))
        self.plot("Costs", "One-way turnover at rebalance", float(turnover))
        self.debug(
            f"[{self.mode.upper()}] {self.time:%Y-%m-%d} rebalance #{self._rebalances}: "
            f"assets={len(targets)} k_expected={k_expected} "
            f"cal_rmse={selection['cal_rmse']:.5f} val_rmse={selection['val_rmse']:.5f} "
            f"turnover={turnover:.1%} checks={checks}"
        )

    def on_end_of_algorithm(self):
        avg_turnover = self._total_turnover / self._rebalances if self._rebalances else 0.0
        self.debug(
            f"[{self.mode.upper()}] done: rebalances={self._rebalances} skipped={self._skipped} "
            f"avg_turnover={avg_turnover:.1%} total_turnover={self._total_turnover:.0%} "
            f"fee={self.fee_bps:.0f}bps/order"
        )
