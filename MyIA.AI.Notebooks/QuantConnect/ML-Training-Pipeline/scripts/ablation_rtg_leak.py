"""
Ablation study: RTG information leak in Decision Transformer trading eval.

PURPOSE:
    Determine whether the "BEATS" verdict in L4/L6 Decision Transformer sweeps
    is driven by genuine learned skill or by the forward-looking Return-To-Go
    (RTG) signal leaked into the model at test time.

    The status quo eval pipeline feeds REALIZED RTG (cumulative future reward)
    into the DT at inference. This is information-theoretically equivalent to
    giving the model a summary of future returns before it predicts the action.

CONDITIONS:
    A. REALIZED-RTG (status quo): feed the realized RTG of each row (leaked).
    B. FIXED-G: replace ALL rtg values in eval sequences with a single CONSTANT
       desired-return prompt = 90th percentile of training-set per-trajectory
       initial RTG. This removes future info while keeping a "aim high" signal.
    C. EXPOSURE-MATCHED NULL (#21187, tranche 3): ``matched_null`` draws of
       condition A. Each draw shuffles A's long-run lengths among themselves
       and its flat-run lengths among themselves, keeping the first state and
       the alternation: exposure and position changes are exactly A's, only
       the timing of the entries changes. C is the mean of the draws.
    C_trades. RANDOM-TIMING (until tranche 3, condition C): random flips with
       a trade frequency matched to A. It matches A in position changes, not
       in exposure, so it is kept for comparison only.

NULL TEST (#21187, tranche 3, protocol published before any measurement):
    For A and B, per fold, 1000 exposure-matched draws of the condition.
    Per symbol and fold, T is the mean over seeds of the condition's Sharpe
    and draw j the mean over seeds of draw j's Sharpe; the fold p-value is
    (1 + draws >= T) / 1001. Fisher's method combines the folds, Holm
    adjusts over the symbols. A symbol shows SKILL under B when its Holm
    p-value is below 0.05; the verdict on B is SKILL-CONFIRMED when at least
    two thirds of the symbols (4 of 6) show it, NO SKILL when none does,
    INCONCLUSIVE otherwise. A - B is reported per symbol, descriptively.

ALIGNMENT (#21187):
    A and B take one decision per step through ``validate_xrp_dt.
    dt_causal_positions``: the decision that drives return k -> k+1 reads
    states on rows <= k-2 and teacher actions on rows <= k-1. The two
    conditions differ only by the RTG fed to the model, so A - B measures the
    RTG leak alone, and C is scored on the same returns. Before #21187 each
    condition applied a window's last argmax about context_length rows before
    the window's last state: both A and B read future states, and results
    produced before that change are not comparable with later ones.

THRESHOLD VERDICT (kept for continuity, not authoritative since tranche 3):
    - "LEAK-DOMINATED" if A >> B ≈ C
    - "PARTIAL-SKILL" if C < B < A
    - "SKILL-CONFIRMED" if B ≈ A and both >> C

SYMBOLS: [SPY, XLF, XLK, IEF, GLD, USO] (6 representative assets)
SEEDS: [0, 1, 7, 42] (4 seeds, L4 default)
WF: 5-fold, L4 defaults for window/context_length/commission

GPU: CUDA_VISIBLE_DEVICES=2 (RTX 4090, shared with co-resident L6 sweep)

NON-DESTRUCTIVE: imports utilities read-only, does not modify any existing script.

Usage:
    python -u ablation_rtg_leak.py
    python -u ablation_rtg_leak.py --symbols SPY QQQ --seeds 0 42
    python -u ablation_rtg_leak.py --smoke
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd
import torch
from scipy.stats import combine_pvalues

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from panier_loader import load_panier
from voltarget_strategy_verdict import holm
from train_rl_dt import (
    DecisionTransformerModel,
    build_trajectories,
    compute_majority_class_baseline,
    evaluate_dt,
    train_dt,
)
from validate_xrp_dt import CAUSAL_EVAL_PROTOCOL, dt_causal_positions

sys.path.insert(0, str(SCRIPTS_DIR.parent / "shared"))
from features import FeatureEngineer

try:
    from walk_forward import WalkForwardSplitter
except ImportError:
    WalkForwardSplitter = None

RESULTS_DIR = SCRIPTS_DIR / "results" / "ablation_rtg_leak"
# C is the exposure-matched null of A since tranche 3; C_trades is the
# trade-matched random timing that was C before (#21187).
CONDITIONS = ("A", "B", "C", "C_trades")


# ---------------------------------------------------------------------------
# Re-use L4 helpers (imported from sweep_l4_decision_transformer where needed)
# ---------------------------------------------------------------------------

import strategy_metrics  # noqa: E402


def compute_sharpe(returns: np.ndarray, annual_factor: int = 252) -> float:
    """Annualized Sharpe (``strategy_metrics.sharpe``: ddof=1, risk-free 0).

    Returns 0.0 for fewer than 10 returns or a standard deviation below 1e-10.
    The formula used the population standard deviation (ddof=0) until #19016:
    the standard deviation grows by ``sqrt(n / (n - 1))``, so the value is
    multiplied by ``sqrt((n - 1) / n)`` -- pinned by the tranche-4 tests.
    """
    if len(returns) < 10 or float(np.std(returns, ddof=1)) < 1e-10:
        return 0.0
    return float(strategy_metrics.sharpe(returns, periods_per_year=annual_factor))


def simulate_dt_portfolio(
    actions: np.ndarray,
    returns: np.ndarray,
    commission_bps: float = 5.0,
) -> np.ndarray:
    """Portfolio returns of an action sequence aligned on the returns it drives.

    Actions: 0=hold, 1=buy (long), 2=sell (flat). ``actions[i]`` sets the
    position held over ``returns[i]``, and a position change pays the
    commission on that same return. Until #21187 the function took a price
    window and paired each action with a return its decision had already
    read past.
    """
    actions = np.asarray(actions)
    returns = np.asarray(returns, dtype=np.float64)
    if len(actions) != len(returns):
        raise ValueError(f"{len(actions)} actions for {len(returns)} returns")
    commission = commission_bps / 10000.0
    position = 0.0
    portfolio_returns = np.zeros(len(returns), dtype=np.float64)

    for i, action in enumerate(actions):
        if action == 1:
            target_pos = 1.0
        elif action == 2:
            target_pos = 0.0  # flat
        else:
            target_pos = position

        trade_cost = abs(target_pos - position) * commission
        portfolio_returns[i] = target_pos * returns[i] - trade_cost
        position = target_pos

    return portfolio_returns


def held_positions(actions: np.ndarray) -> np.ndarray:
    """Position held after each action (1 = long, 0 = flat), starting flat."""
    positions = np.zeros(len(actions), dtype=np.float64)
    position = 0.0
    for i, action in enumerate(actions):
        if action == 1:
            position = 1.0
        elif action == 2:
            position = 0.0
        positions[i] = position
    return positions


def count_trades(actions: np.ndarray) -> int:
    """Position changes, i.e. commissions ``simulate_dt_portfolio`` charges.

    Before #21187 the ablation counted action-label changes: a lone buy
    between two holds counted twice though it moves the position once, and a
    buy issued while already long counted though it moves nothing.
    """
    positions = held_positions(actions)
    return int(np.sum(np.diff(np.concatenate([[0.0], positions])) != 0))


def score_actions(
    actions: np.ndarray,
    returns: np.ndarray,
    commission_bps: float = 5.0,
) -> dict:
    """Metrics shared by the three conditions, on the same aligned returns."""
    actions = np.asarray(actions, dtype=np.int64)
    returns = np.asarray(returns, dtype=np.float64)
    dt_rets = simulate_dt_portfolio(actions, returns, commission_bps=commission_bps)
    sharpe_dt = compute_sharpe(dt_rets)
    sharpe_bh = compute_sharpe(returns)
    # Direction accuracy of the buy label: a buy is right when the return it
    # drives is up. Despite its key name it is an accuracy, not an AUC.
    auc = float(((actions == 1) == (returns > 0)).mean()) if len(actions) else 0.5
    positions = held_positions(actions)
    # Same accuracy on the held position: the only one the null can share.
    hit_rate = float(((positions > 0) == (returns > 0)).mean()) if len(actions) else 0.5
    n_trades = count_trades(actions)
    # Share of returns held long: C matches A in trades, not in exposure.
    exposure = float(positions.mean()) if len(actions) else 0.0
    return {
        "sharpe_dt": round(sharpe_dt, 4),
        "sharpe_bh": round(sharpe_bh, 4),
        "delta_sharpe": round(sharpe_dt - sharpe_bh, 4),
        "auc": round(auc, 4),
        "hit_rate": round(hit_rate, 4),
        "n_trades": n_trades,
        "exposure": round(exposure, 4),
        "n_preds": int(len(actions)),
    }


# ---------------------------------------------------------------------------
# Exposure-matched null (#21187, tranche 3)
# ---------------------------------------------------------------------------

# A draw identical to the condition can differ from it by float rounding:
# ties are counted against the condition.
NULL_TIE_TOL = 1e-9
SKILL_ALPHA = 0.05


def position_returns(
    positions: np.ndarray,
    returns: np.ndarray,
    commission_bps: float = 5.0,
) -> np.ndarray:
    """Portfolio returns of held positions, one row per position sequence.

    Same accounting as ``simulate_dt_portfolio``: the position held over
    ``returns[i]`` earns it, and a change from the previous position (flat
    before the first return) pays the commission on that same return.
    """
    pos = np.atleast_2d(np.asarray(positions, dtype=np.float64))
    returns = np.asarray(returns, dtype=np.float64)
    prev = np.concatenate([np.zeros((pos.shape[0], 1)), pos[:, :-1]], axis=1)
    return pos * returns - np.abs(pos - prev) * (commission_bps / 10000.0)


def row_sharpes(port: np.ndarray) -> np.ndarray:
    """``compute_sharpe`` of each row, vectorized."""
    port = np.atleast_2d(np.asarray(port, dtype=np.float64))
    if port.shape[1] < 10:
        return np.zeros(port.shape[0])
    flat = port.std(axis=1, ddof=1) < 1e-10
    with np.errstate(divide="ignore", invalid="ignore"):
        values = strategy_metrics.sharpe(port, axis=1)
    return np.where(flat, 0.0, values)


def permute_runs(positions: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    """One draw of the exposure-matched null.

    Splits ``positions`` into runs of constant position, shuffles the
    long-run lengths among themselves and the flat-run lengths among
    themselves, and keeps the first state and the alternation. The draw has
    exactly the exposure and the position changes of ``positions``: only
    the timing of the entries changes.
    """
    pos = np.asarray(positions, dtype=np.float64)
    if len(pos) == 0:
        return pos.copy()
    starts = np.concatenate([[0], np.flatnonzero(np.diff(pos) != 0) + 1])
    lengths = np.diff(np.concatenate([starts, [len(pos)]]))
    states = pos[starts]
    shuffled = lengths.copy()
    for mask in (states > 0, states <= 0):
        shuffled[mask] = rng.permutation(lengths[mask])
    return np.repeat(states, shuffled)


def matched_null(
    actions: np.ndarray,
    returns: np.ndarray,
    n_draws: int = 1000,
    commission_bps: float = 5.0,
    rng: np.random.Generator | None = None,
) -> dict:
    """Sharpe of ``actions`` and of ``n_draws`` exposure-matched draws.

    ``sharpe`` is the unrounded statistic, computed by the same vectorized
    path as the draws so that a draw identical to the condition ties with
    it. ``null`` holds the draws' Sharpe ratios in draw order: draw j of
    every seed is averaged into draw j of the symbol's null. ``hit_rate``
    is the mean over draws of the share of returns whose sign matches the
    held position, as the ``hit_rate`` of ``score_actions``; the null has no
    action labels, so it has no ``auc``.
    """
    rng = rng if rng is not None else np.random.default_rng(0)
    returns = np.asarray(returns, dtype=np.float64)
    positions = held_positions(actions)
    draws = np.stack([permute_runs(positions, rng) for _ in range(n_draws)])
    sharpe = float(row_sharpes(position_returns(positions, returns, commission_bps))[0])
    null = row_sharpes(position_returns(draws, returns, commission_bps))
    hit_rate = float(((draws > 0) == (returns > 0)).mean())
    return {"sharpe": sharpe, "null": null, "hit_rate": hit_rate}


def null_condition_row(res_a: dict, null_a: dict) -> dict:
    """Fold row of condition C: the mean of A's exposure-matched null.

    The null has no action labels: its row carries ``hit_rate`` (sign of the
    held position against the return, as for A and B) and ``auc`` is None,
    so that no column compares an accuracy of A's labels with the null.
    """
    null_mean = float(null_a["null"].mean())
    return {
        "sharpe_dt": round(null_mean, 4),
        "sharpe_bh": res_a["sharpe_bh"],
        "delta_sharpe": round(null_mean - res_a["sharpe_bh"], 4),
        "auc": None,
        "hit_rate": round(null_a["hit_rate"], 4),
        "n_trades": res_a["n_trades"],
        "exposure": res_a["exposure"],
        "n_preds": res_a["n_preds"],
    }


def null_p_value(statistic: float, null: np.ndarray) -> float:
    """(1 + draws at or above the statistic) / (1 + draws)."""
    null = np.asarray(null, dtype=np.float64)
    return float((1 + np.sum(null >= statistic - NULL_TIE_TOL)) / (1 + len(null)))


def symbol_null_test(per_seed: list[dict]) -> dict:
    """Pre-registered test of one condition on one symbol.

    ``per_seed`` holds one ``{fold: (sharpe, null)}`` mapping per seed. Per
    fold, T is the mean over seeds of the Sharpe and draw j of the null the
    mean over seeds of draw j; Fisher's method combines the fold p-values
    (the test windows are disjoint).
    """
    folds = sorted(set().union(*per_seed))
    rows = []
    for fold in folds:
        entries = [d[fold] for d in per_seed if fold in d]
        statistic = float(np.mean([s for s, _ in entries]))
        null = np.mean(np.stack([n for _, n in entries]), axis=0)
        rows.append({
            "fold": int(fold),
            "n_seeds": len(entries),
            "sharpe": round(statistic, 4),
            "null_mean": round(float(null.mean()), 4),
            "null_sd": round(float(null.std(ddof=1)), 4) if len(null) > 1 else 0.0,
            "p": null_p_value(statistic, null),
            "_sharpe": statistic,
        })
    p_values = [r["p"] for r in rows]
    fisher_p = float(combine_pvalues(p_values, method="fisher").pvalue) if p_values else 1.0
    return {"folds": rows, "fisher_p": fisher_p}


def skill_verdict(p_holm: dict[str, float], alpha: float = SKILL_ALPHA) -> tuple[str, list[str]]:
    """Pre-registered verdict from the Holm-adjusted p-values of the symbols.

    SKILL-CONFIRMED when at least two thirds of the symbols (4 of the 6 of
    the protocol) are below ``alpha``, NO SKILL when none is, INCONCLUSIVE
    otherwise.
    """
    skilled = sorted(s for s, p in p_holm.items() if p < alpha)
    if not p_holm:
        return "INCONCLUSIVE", skilled
    if len(skilled) >= math.ceil(2 * len(p_holm) / 3):
        return "SKILL-CONFIRMED", skilled
    if not skilled:
        return "NO SKILL", skilled
    return "INCONCLUSIVE", skilled


# ---------------------------------------------------------------------------
# Core ablation logic
# ---------------------------------------------------------------------------

def compute_train_rtg_p90(
    train_prices: np.ndarray,
    train_features_norm: np.ndarray,
    window: int = 20,
    context_length: int = 20,
    commission_bps: float = 5.0,
) -> float:
    """Compute the 90th percentile of per-trajectory initial RTG from training data.

    'Initial RTG' = RTG at the first timestep of each trajectory segment,
    which is the cumulative future reward from that point to end of the price
    series. The 90th percentile represents a 'high but not extreme' desired
    return prompt for condition B.

    Returns:
        float: the 90th percentile value.
    """
    trajs = build_trajectories(
        train_prices, train_features_norm,
        window=window, context_length=context_length,
        commission=commission_bps / 10000.0,
    )
    rtg_vals = trajs["rtg"].flatten()
    # The first `context_length` entries are the initial RTGs for segments
    # starting at positions [start_idx, start_idx + context_length).
    # But actually build_trajectories returns one entry per timestep from
    # start_idx to n-context_length. The 'initial RTG' for the first
    # segment of length context_length is rtg[0].
    # For the 90th percentile of 'per-trajectory initial RTG', we sample
    # every context_length-th entry (non-overlapping segments).
    n = len(rtg_vals)
    n_segments = n // context_length
    if n_segments == 0:
        return float(np.percentile(rtg_vals, 90))

    initial_rtgs = []
    for i in range(n_segments):
        idx = i * context_length
        if idx < n:
            initial_rtgs.append(rtg_vals[idx])

    return float(np.percentile(initial_rtgs, 90))


def causal_eval_returns(
    test_prices: np.ndarray,
    window: int = 20,
    context_length: int = 20,
) -> np.ndarray:
    """Test returns driven by a DT decision: k -> k+1 for k >= window + context_length."""
    returns = np.diff(test_prices) / (test_prices[:-1] + 1e-8)
    return returns[window + context_length:]


def realized_rtg_rows(
    test_prices: np.ndarray,
    test_features_norm: np.ndarray,
    window: int = 20,
    commission_bps: float = 5.0,
) -> np.ndarray:
    """Realized RTG of each test row, as ``build_trajectories`` computes it.

    ``rtg[t]`` sums the teacher rewards from row t to the end of the test set:
    it reads every later price. Condition A feeds it on purpose. Rows before
    ``window`` carry no trajectory and stay at 0; ``dt_causal_positions``
    never reads them.
    """
    trajs = build_trajectories(
        test_prices, test_features_norm,
        window=window, context_length=1,
        commission=commission_bps / 10000.0,
    )
    vals = np.asarray(trajs["rtg"], dtype=np.float32).reshape(-1)
    rtg = np.zeros(len(test_prices), dtype=np.float32)
    rtg[window:window + len(vals)] = vals
    return rtg


def causal_condition_actions(
    model: DecisionTransformerModel,
    test_prices: np.ndarray,
    test_features_norm: np.ndarray,
    rtg_rows: np.ndarray,
    context_length: int = 20,
    window: int = 20,
    device: str = "cpu",
) -> np.ndarray:
    """DT actions, one per return of ``causal_eval_returns`` (#21187).

    Wraps ``dt_causal_positions``: the decision that drives return k -> k+1
    reads states on rows <= k-2 and teacher actions on rows <= k-1. Conditions
    A and B differ only by ``rtg_rows``, so their gap measures the RTG leak
    alone. Before #21187 each condition took every window's last argmax and
    applied it about context_length rows before the window's last state.
    """
    positions, first_k = dt_causal_positions(
        model, test_prices, test_features_norm, window, context_length,
        rtg_per_step=0.0, batch_size=64, device=device, rtg_rows=rtg_rows,
    )
    # dt_causal_positions maps argmax 1 -> +1, 2 -> -1, 0 -> 0: invert it.
    actions = np.where(positions > 0, 1, np.where(positions < 0, 2, 0))
    return actions[first_k:].astype(np.int64)


def run_condition_a(
    model: DecisionTransformerModel,
    test_prices: np.ndarray,
    test_features_norm: np.ndarray,
    context_length: int = 20,
    window: int = 20,
    commission_bps: float = 5.0,
    device: str = "cpu",
) -> dict:
    """Condition A: REALIZED-RTG (leaked through the RTG only).

    Same causal alignment as condition B; the input RTG is the realized one.
    ``actions`` is returned with the metrics for the exposure-matched null.
    """
    rtg_rows = realized_rtg_rows(
        test_prices, test_features_norm, window=window,
        commission_bps=commission_bps,
    )
    actions = causal_condition_actions(
        model, test_prices, test_features_norm, rtg_rows,
        context_length=context_length, window=window, device=device,
    )
    if len(actions) < 10:
        return {"error": "too few predictions"}
    returns = causal_eval_returns(test_prices, window, context_length)
    result = score_actions(actions, returns, commission_bps=commission_bps)
    result["actions"] = actions
    return result


def run_condition_b(
    model: DecisionTransformerModel,
    test_prices: np.ndarray,
    test_features_norm: np.ndarray,
    fixed_g: float,
    context_length: int = 20,
    window: int = 20,
    commission_bps: float = 5.0,
    device: str = "cpu",
) -> dict:
    """Condition B: FIXED-G (constant desired return prompt).

    Every RTG the model sees is ``fixed_g``: no future information enters
    through the RTG, and the causal alignment keeps it out of the states and
    actions too.
    """
    rtg_rows = np.full(len(test_prices), fixed_g, dtype=np.float32)
    actions = causal_condition_actions(
        model, test_prices, test_features_norm, rtg_rows,
        context_length=context_length, window=window, device=device,
    )
    if len(actions) < 10:
        return {"error": "too few predictions"}
    returns = causal_eval_returns(test_prices, window, context_length)
    result = score_actions(actions, returns, commission_bps=commission_bps)
    result["fixed_g"] = round(fixed_g, 6)
    result["actions"] = actions
    return result


def run_condition_c(
    returns: np.ndarray,
    n_trades_target: int,
    commission_bps: float = 5.0,
    seed: int = 42,
) -> dict:
    """Condition C_trades: RANDOM-TIMING baseline (condition C until tranche 3).

    Generate random actions with trade frequency matched to condition A.
    It does not match A in exposure (on the tranche-2 smoke run, 36-41 % of
    SPY's returns held long against 70-73 % for A and B): since tranche 3 the
    verdict uses ``matched_null`` instead, and this condition is reported for
    comparison only.
    This isolates the cash-timing Sharpe artifact: a variable-sizing
    portfolio that periodically holds cash can beat buy-and-hold Sharpe
    even with ZERO directional skill (volatility reduction).

    Method:
        1. Compute target trade count from condition A (n_trades_target),
           counted as position changes (``count_trades``).
        2. Compute target trade probability = n_trades_target / n_preds.
        3. At each timestep, with that probability, flip the position
           (buy when flat, go flat when long). Otherwise hold.
        4. Score these actions on the returns of conditions A and B.

    Before #21187 a trade event drew long or flat at random, so about half
    the events left the position unchanged, and the target and the reported
    count were action-label changes: A and C were not matched in trades.
    """
    rng = np.random.RandomState(seed + 1000)  # offset seed to decorrelate
    n_preds = len(returns)

    # Compute trade probability
    if n_preds < 2 or n_trades_target < 1:
        trade_prob = 0.1  # fallback
    else:
        trade_prob = min(n_trades_target / n_preds, 0.8)

    # Generate random actions
    random_actions = np.zeros(n_preds, dtype=np.int64)
    position = 0
    for i in range(1, n_preds):
        if rng.random() < trade_prob:
            position = 1 - position
            random_actions[i] = 1 if position == 1 else 2  # buy / flat (sell)
        else:
            random_actions[i] = 0  # hold

    result = score_actions(random_actions, returns, commission_bps=commission_bps)
    result["trade_prob"] = round(trade_prob, 4)
    return result


def run_single_ablation(
    symbol: str,
    seed: int,
    raw: pd.DataFrame,
    n_splits: int = 5,
    d_model: int = 128,
    nhead: int = 4,
    num_layers: int = 3,
    context_length: int = 20,
    epochs_per_fold: int = 15,
    window: int = 20,
    lookback: int = 20,
    commission_bps: float = 5.0,
    device: str = "cpu",
    n_null: int = 1000,
) -> dict:
    """Run full 3-condition ablation for one (symbol, seed) combo.

    Walk-forward 5-fold. For each fold:
        1. Train DT on train set (standard, with realized RTG -- training is fine)
        2. Compute fixed_g from train set (90th pctile of initial RTG)
        3. Evaluate condition A (realized RTG) on test
        4. Evaluate condition B (fixed-G) on test
        5. Draw the exposure-matched nulls of A and B (C = A's null mean)
        6. Evaluate condition C_trades (random timing) on test

    Aggregate across folds: mean dSharpe, std, AUC, trades. ``_null`` carries
    ``{condition: {fold: (sharpe, null draws)}}`` for the symbol-level test;
    ``main`` removes it before writing the JSON.
    """
    np.random.seed(seed)
    torch.manual_seed(seed)

    # Feature engineering
    indicators = [
        "returns", "volatility", "volume_ratio", "ma_ratios",
        "rsi", "macd", "bollinger", "true_range_atr", "obv",
    ]
    engineer = FeatureEngineer(lookback=lookback, indicators=indicators)
    features_df = engineer.transform(raw, add_target=False)
    features_arr = features_df.values.astype(np.float32)
    prices = raw.loc[features_df.index, "Close"].values.astype(np.float32)

    n = len(prices)
    if n < 500:
        return {"error": f"insufficient data ({n} rows)"}

    if WalkForwardSplitter is None:
        return {"error": "WalkForwardSplitter not available"}

    splitter = WalkForwardSplitter(
        n_splits=n_splits,
        train_size=max(252, n // (n_splits + 1)),
        test_size=max(63, n // (n_splits * 3)),
        gap=24,
    )

    fold_results = {cond: [] for cond in CONDITIONS}
    null_draws = {"A": {}, "B": {}}
    fixed_g_values = []

    for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(np.arange(n))):
        if len(test_idx) < context_length + window + 10:
            continue

        # Normalize features on train only
        train_feat = features_arr[train_idx]
        mean = train_feat.mean(axis=0)
        std = train_feat.std(axis=0)
        std = np.where(std < 1e-8, 1.0, std)

        train_features_norm = (features_arr[train_idx] - mean) / std
        test_features_norm = (features_arr[test_idx] - mean) / std

        train_prices = prices[train_idx]
        test_prices = prices[test_idx]

        # Build training trajectories
        train_trajs = build_trajectories(
            train_prices, train_features_norm,
            window=window, context_length=context_length,
            commission=commission_bps / 10000.0,
        )

        if len(train_trajs["states"]) <= context_length:
            continue

        state_dim = train_trajs["states"].shape[1]

        # Train DT (standard -- RTG leak in training is by design for DT)
        result = train_dt(
            train_trajs,
            state_dim=state_dim,
            d_model=d_model,
            nhead=nhead,
            num_layers=num_layers,
            context_length=context_length,
            epochs=epochs_per_fold,
            batch_size=32,
            lr=1e-4,
            device=device,
        )
        model = result["model"]

        # Compute fixed_g from training set
        fixed_g = compute_train_rtg_p90(
            train_prices, train_features_norm,
            window=window, context_length=context_length,
            commission_bps=commission_bps,
        )
        fixed_g_values.append(fixed_g)

        # Condition A: realized RTG (leaked), causal alignment (#21187)
        res_a = run_condition_a(
            model, test_prices, test_features_norm,
            context_length=context_length, window=window,
            commission_bps=commission_bps, device=device,
        )
        # Condition B: fixed-G, same alignment
        res_b = run_condition_b(
            model, test_prices, test_features_norm,
            fixed_g=fixed_g,
            context_length=context_length, window=window,
            commission_bps=commission_bps, device=device,
        )
        eval_returns = causal_eval_returns(test_prices, window, context_length)

        # Exposure-matched nulls of A and B on the same returns (tranche 3).
        nulls = {}
        for code, (cond, res) in enumerate((("A", res_a), ("B", res_b))):
            if "error" in res:
                continue
            fold_results[cond].append(res)
            nulls[cond] = matched_null(
                res.pop("actions"), eval_returns, n_draws=n_null,
                commission_bps=commission_bps,
                rng=np.random.default_rng([seed, fold_idx, code]),
            )
            null_draws[cond][fold_idx] = (nulls[cond]["sharpe"], nulls[cond]["null"])

        # Condition C: A's null, i.e. A's exposure and position changes.
        if "A" in nulls:
            fold_results["C"].append(null_condition_row(res_a, nulls["A"]))

        # Condition C_trades: random timing on the same returns (trade count from A)
        res_c = run_condition_c(
            eval_returns,
            n_trades_target=res_a.get("n_trades", 10),
            commission_bps=commission_bps,
            seed=seed,
        )
        if "error" not in res_c:
            fold_results["C_trades"].append(res_c)

    # Aggregate across folds
    agg = {}
    for cond in CONDITIONS:
        folds = fold_results[cond]
        if not folds:
            agg[cond] = {"error": "no valid folds"}
            continue

        deltas = [f["delta_sharpe"] for f in folds]
        aucs = [f["auc"] for f in folds if f.get("auc") is not None]
        trades = [f["n_trades"] for f in folds]

        agg[cond] = {
            "mean_dSharpe": round(float(np.mean(deltas)), 4),
            "std_dSharpe": round(float(np.std(deltas)), 4),
            "t_stat": round(float(np.mean(deltas) / (np.std(deltas) + 1e-10)), 4),
            "mean_auc": round(float(np.mean(aucs)), 4) if aucs else None,
            "mean_hit_rate": round(float(np.mean([f["hit_rate"] for f in folds])), 4),
            "mean_trades": int(np.mean(trades)),
            "mean_exposure": round(float(np.mean([f["exposure"] for f in folds])), 4),
            "n_folds": len(folds),
            "fold_deltas": [round(d, 4) for d in deltas],
        }

    agg["fixed_g_mean"] = round(float(np.mean(fixed_g_values)), 6) if fixed_g_values else None
    agg["fixed_g_values"] = [round(g, 6) for g in fixed_g_values]
    # Fingerprint of the evaluated prices, so a re-run can be compared (#21187).
    agg["data_sha256"] = hashlib.sha256(prices.tobytes()).hexdigest()[:16]
    # Per-seed view of the null test (descriptive; the test pools the seeds).
    agg["null_folds"] = {
        cond: [
            {
                "fold": int(fold),
                "sharpe": round(stat, 4),
                "null_mean": round(float(null.mean()), 4),
                "p": null_p_value(stat, null),
            }
            for fold, (stat, null) in sorted(draws.items())
        ]
        for cond, draws in null_draws.items()
    }
    agg["_null"] = null_draws

    return agg


def main():
    parser = argparse.ArgumentParser(description="RTG leak ablation for Decision Transformer")
    parser.add_argument("--symbols", nargs="+",
                        default=["SPY", "XLF", "XLK", "IEF", "GLD", "USO"],
                        help="Symbols to test")
    parser.add_argument("--seeds", nargs="+", type=int, default=[0, 1, 7, 42],
                        help="Random seeds")
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--epochs-per-fold", type=int, default=15)
    parser.add_argument("--d-model", type=int, default=128)
    parser.add_argument("--nhead", type=int, default=4)
    parser.add_argument("--num-layers", type=int, default=3)
    parser.add_argument("--context-length", type=int, default=20)
    parser.add_argument("--window", type=int, default=20)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--commission-bps", type=float, default=5.0)
    parser.add_argument("--n-null", type=int, default=1000,
                        help="Exposure-matched draws per condition and fold")
    parser.add_argument("--smoke", action="store_true",
                        help="Quick test: 2 symbols, 2 seeds, 2 epochs")
    parser.add_argument("--output", type=str, default=None)
    args = parser.parse_args()

    # Device
    device = "cuda" if torch.cuda.is_available() else "cpu"
    print(f"Device: {device} | torch {torch.__version__}")

    # Smoke test
    if args.smoke:
        args.symbols = args.symbols[:2]
        args.seeds = args.seeds[:2]
        args.epochs_per_fold = 2
        args.n_splits = 2
        print("SMOKE MODE: 2 symbols, 2 seeds, 2 epochs, 2 folds")

    symbols = args.symbols
    seeds = args.seeds
    n_combos = len(symbols) * len(seeds)
    print(f"Ablation: {len(symbols)} symbols x {len(seeds)} seeds = {n_combos} combos")
    print(f"  Conditions: A=realized-RTG (leaked), B=fixed-G, "
          f"C=exposure-matched null of A, C_trades=random-timing")
    print(f"  WF folds={args.n_splits}, epochs/fold={args.epochs_per_fold}, "
          f"commission={args.commission_bps}bps, null draws={args.n_null}")

    # Load panier
    panier = load_panier(start="2015-01-01", auto_fetch=True)
    loaded_symbols = [s for s in symbols if s in panier]
    if len(loaded_symbols) < len(symbols):
        missing = [s for s in symbols if s not in panier]
        print(f"WARNING: {len(missing)} symbols not in panier: {missing}")
    symbols = loaded_symbols

    print(f"Loaded panier: {len(symbols)} symbols")

    # Run ablation
    t0 = time.time()
    combo_idx = 0
    all_results = {}
    null_store = {}

    for symbol in symbols:
        raw = panier[symbol]
        all_results[symbol] = {}
        null_store[symbol] = {}

        for seed in seeds:
            combo_idx += 1
            print(f"\n[{combo_idx}/{n_combos}] {symbol} seed={seed}")
            print(f"  Running 3-condition ablation...", flush=True)

            try:
                result = run_single_ablation(
                    symbol=symbol,
                    seed=seed,
                    raw=raw,
                    n_splits=args.n_splits,
                    d_model=args.d_model,
                    nhead=args.nhead,
                    num_layers=args.num_layers,
                    context_length=args.context_length,
                    epochs_per_fold=args.epochs_per_fold,
                    window=args.window,
                    lookback=args.lookback,
                    commission_bps=args.commission_bps,
                    device=device,
                    n_null=args.n_null,
                )
                null_store[symbol][seed] = result.pop("_null", {})
                all_results[symbol][seed] = result

                # Print per-combo summary
                for cond in CONDITIONS:
                    if cond in result and "error" not in result.get(cond, {}):
                        r = result[cond]
                        print(f"  Cond {cond}: dSharpe={r['mean_dSharpe']:+.4f} "
                              f"(std={r['std_dSharpe']:.4f}, t={r['t_stat']:.2f}) "
                              f"hit_rate={r['mean_hit_rate']:.4f} trades={r['mean_trades']}")
                    else:
                        print(f"  Cond {cond}: ERROR")
                if result.get("fixed_g_mean"):
                    print(f"  Fixed-G value: {result['fixed_g_mean']:.6f}")

            except Exception as e:
                print(f"  EXCEPTION: {e}")
                import traceback
                traceback.print_exc()
                all_results[symbol][seed] = {"error": str(e)}

    # ===================================================================
    # Aggregate results: symbol x condition -> cross-seed stats
    # ===================================================================
    print(f"\n{'='*80}")
    print("ABLATION RESULTS TABLE")
    print(f"{'='*80}")
    print(f"{'Symbol':<8} {'Cond':<9} {'Mean dS':>10} {'Std':>8} {'t-stat':>8} "
          f"{'Hit rate':>10} {'Trades':>8}")
    print("-" * 71)

    # Per-symbol aggregation
    table = {}
    for symbol in symbols:
        table[symbol] = {}
        for cond in CONDITIONS:
            deltas = []
            aucs = []
            hits = []
            trades = []
            for seed in seeds:
                res = all_results.get(symbol, {}).get(seed, {})
                cond_data = res.get(cond, {})
                if "error" in cond_data:
                    continue
                deltas.append(cond_data["mean_dSharpe"])
                if cond_data.get("mean_auc") is not None:
                    aucs.append(cond_data["mean_auc"])
                hits.append(cond_data["mean_hit_rate"])
                trades.append(cond_data["mean_trades"])

            if deltas:
                mean_d = float(np.mean(deltas))
                std_d = float(np.std(deltas))
                t_stat = mean_d / (std_d + 1e-10)
                mean_hit = float(np.mean(hits))
                mean_trades = int(np.mean(trades))
                table[symbol][cond] = {
                    "mean_dSharpe": round(mean_d, 4),
                    "std_dSharpe": round(std_d, 4),
                    "t_stat": round(t_stat, 4),
                    "mean_auc": round(float(np.mean(aucs)), 4) if aucs else None,
                    "mean_hit_rate": round(mean_hit, 4),
                    "mean_trades": mean_trades,
                    "n_seeds": len(deltas),
                }
                print(f"{symbol:<8} {cond:<9} {mean_d:>+10.4f} {std_d:>8.4f} "
                      f"{t_stat:>8.4f} {mean_hit:>10.4f} {mean_trades:>8d}")
            else:
                table[symbol][cond] = {"error": "no valid seeds"}
                print(f"{symbol:<8} {cond:<9} {'ERROR':>10}")

    # Per-condition aggregate (all symbols pooled)
    print("-" * 71)
    agg_table = {}
    for cond in CONDITIONS:
        all_deltas = []
        all_aucs = []
        all_hits = []
        all_trades = []
        for symbol in symbols:
            if cond in table.get(symbol, {}) and "error" not in table[symbol].get(cond, {}):
                all_deltas.append(table[symbol][cond]["mean_dSharpe"])
                if table[symbol][cond]["mean_auc"] is not None:
                    all_aucs.append(table[symbol][cond]["mean_auc"])
                all_hits.append(table[symbol][cond]["mean_hit_rate"])
                all_trades.append(table[symbol][cond]["mean_trades"])

        if all_deltas:
            mean_d = float(np.mean(all_deltas))
            std_d = float(np.std(all_deltas))
            t_stat = mean_d / (std_d + 1e-10)
            mean_hit = float(np.mean(all_hits))
            mean_trades = int(np.mean(all_trades))
            agg_table[cond] = {
                "mean_dSharpe": round(mean_d, 4),
                "std_dSharpe": round(std_d, 4),
                "t_stat": round(t_stat, 4),
                "mean_auc": round(float(np.mean(all_aucs)), 4) if all_aucs else None,
                "mean_hit_rate": round(mean_hit, 4),
                "mean_trades": mean_trades,
                "n_symbols": len(all_deltas),
            }
            print(f"{'ALL':<8} {cond:<9} {mean_d:>+10.4f} {std_d:>8.4f} "
                  f"{t_stat:>8.4f} {mean_hit:>10.4f} {mean_trades:>8d}")
        else:
            agg_table[cond] = {"error": "no data"}
            print(f"{'ALL':<8} {cond:<9} {'ERROR':>10}")

    # ===================================================================
    # Pre-registered null test (#21187, tranche 3)
    # ===================================================================
    print(f"\n{'='*80}")
    print("EXPOSURE-MATCHED NULL TEST (pre-registered, authoritative)")
    print(f"{'='*80}")
    null_tests = {}
    for cond in ("A", "B"):
        per_symbol = {}
        for symbol in symbols:
            per_seed = [null_store[symbol][s][cond] for s in seeds
                        if null_store.get(symbol, {}).get(s, {}).get(cond)]
            if per_seed:
                per_symbol[symbol] = symbol_null_test(per_seed)
        adjusted = holm({s: r["fisher_p"] for s, r in per_symbol.items()})
        for symbol, res in per_symbol.items():
            res["p_holm"] = adjusted[symbol]
            res["skill"] = adjusted[symbol] < SKILL_ALPHA
        cond_verdict, skilled = skill_verdict(adjusted)
        null_tests[cond] = {"verdict": cond_verdict, "skilled": skilled,
                            "per_symbol": per_symbol}

    print(f"{'Symbol':<8} {'Cond':<5} {'Sharpe':>8} {'Null':>8} {'p Fisher':>10} "
          f"{'p Holm':>8}  folds p")
    for symbol in symbols:
        for cond in ("A", "B"):
            res = null_tests[cond]["per_symbol"].get(symbol)
            if res is None:
                print(f"{symbol:<8} {cond:<5} {'NO DATA':>8}")
                continue
            sharpe = np.mean([r["_sharpe"] for r in res["folds"]])
            null_mean = np.mean([r["null_mean"] for r in res["folds"]])
            fold_ps = " ".join(f"{r['p']:.3f}" for r in res["folds"])
            print(f"{symbol:<8} {cond:<5} {sharpe:>+8.3f} {null_mean:>+8.3f} "
                  f"{res['fisher_p']:>10.4f} {res['p_holm']:>8.4f}  {fold_ps}")

    # A - B: the RTG leak, per symbol, on the folds both conditions scored.
    leak = {}
    for symbol in symbols:
        a_res = null_tests["A"]["per_symbol"].get(symbol)
        b_res = null_tests["B"]["per_symbol"].get(symbol)
        if not (a_res and b_res):
            continue
        a_by_fold = {r["fold"]: r["_sharpe"] for r in a_res["folds"]}
        b_by_fold = {r["fold"]: r["_sharpe"] for r in b_res["folds"]}
        common = sorted(set(a_by_fold) & set(b_by_fold))
        if common:
            leak[symbol] = round(float(np.mean(
                [a_by_fold[f] - b_by_fold[f] for f in common])), 4)
    print(f"\n  A - B (Sharpe, mean over folds and seeds): "
          + ", ".join(f"{s} {d:+.3f}" for s, d in leak.items()))
    for cond in ("A", "B"):
        print(f"  Verdict {cond}: {null_tests[cond]['verdict']} "
              f"(SKILL: {', '.join(null_tests[cond]['skilled']) or 'none'})")
    for cond in ("A", "B"):
        for res in null_tests[cond]["per_symbol"].values():
            for row in res["folds"]:
                row.pop("_sharpe", None)

    # ===================================================================
    # Verdict
    # ===================================================================
    print(f"\n{'='*80}")
    print("THRESHOLD VERDICT (continuity only; C = mean of A's matched null)")
    print(f"{'='*80}")

    # Check conditions for verdict
    a_agg = agg_table.get("A", {})
    b_agg = agg_table.get("B", {})
    c_agg = agg_table.get("C", {})

    a_mean = a_agg.get("mean_dSharpe", 0)
    b_mean = b_agg.get("mean_dSharpe", 0)
    c_mean = c_agg.get("mean_dSharpe", 0)

    print(f"  A (leaked) mean dSharpe: {a_mean:+.4f}")
    print(f"  B (fixed-G) mean dSharpe: {b_mean:+.4f}")
    print(f"  C (null A)  mean dSharpe: {c_mean:+.4f}")

    a_b_diff = abs(a_mean - b_mean)
    b_c_diff = abs(b_mean - c_mean)
    a_c_diff = abs(a_mean - c_mean)

    print(f"  |A - B| = {a_b_diff:.4f}")
    print(f"  |B - C| = {b_c_diff:.4f}")
    print(f"  |A - C| = {a_c_diff:.4f}")

    # Verdict logic:
    # LEAK-DOMINATED: A >> B ≈ C  (i.e. A-B large, B-C small)
    # PARTIAL-SKILL:  C < B < A   (B is between C and A)
    # SKILL-CONFIRMED: B ≈ A and both >> C

    threshold_ratio = 2.0  # B must be within 50% of the other to count as "≈"
    a_abs = abs(a_mean)
    c_abs = abs(c_mean) if abs(c_mean) > 0.001 else 0.001

    if a_abs > 0.001:
        # Normalize differences
        b_close_to_c = b_c_diff < a_abs * 0.3  # B is within 30% of A's range to C
        b_close_to_a = a_b_diff < a_abs * 0.3  # B is within 30% of A
        a_far_from_c = a_c_diff > a_abs * 0.5

        if b_close_to_c and a_far_from_c:
            verdict = "LEAK-DOMINATED"
            reason = (f"A >> B ≈ C: leaked-RTG (A={a_mean:+.4f}) far above "
                      f"fixed-G (B={b_mean:+.4f}) ≈ random (C={c_mean:+.4f}). "
                      f"|A-B|={a_b_diff:.4f} >> |B-C|={b_c_diff:.4f}")
        elif b_close_to_a and a_far_from_c:
            verdict = "SKILL-CONFIRMED"
            reason = (f"B ≈ A >> C: fixed-G (B={b_mean:+.4f}) ≈ leaked (A={a_mean:+.4f}) "
                      f"both >> random (C={c_mean:+.4f}). "
                      f"|A-B|={a_b_diff:.4f} << |A-C|={a_c_diff:.4f}")
        elif c_mean < b_mean < a_mean:
            verdict = "PARTIAL-SKILL"
            reason = (f"C < B < A: random (C={c_mean:+.4f}) < fixed-G (B={b_mean:+.4f}) "
                      f"< leaked (A={a_mean:+.4f}). Some skill, but RTG inflates.")
        else:
            verdict = "INCONCLUSIVE"
            reason = f"No clear pattern: A={a_mean:+.4f}, B={b_mean:+.4f}, C={c_mean:+.4f}"
    else:
        verdict = "INCONCLUSIVE"
        reason = f"All conditions near zero: A={a_mean:+.4f}, B={b_mean:+.4f}, C={c_mean:+.4f}"

    print(f"\n  VERDICT: {verdict}")
    print(f"  REASON:  {reason}")

    # Per-symbol verdict
    print(f"\n  Per-symbol verdicts:")
    for symbol in symbols:
        a_s = table.get(symbol, {}).get("A", {}).get("mean_dSharpe", 0)
        b_s = table.get(symbol, {}).get("B", {}).get("mean_dSharpe", 0)
        c_s = table.get(symbol, {}).get("C", {}).get("mean_dSharpe", 0)

        if a_s == 0 and b_s == 0:
            sym_verdict = "NO-DATA"
        elif abs(b_s - c_s) < abs(a_s) * 0.3 and abs(a_s) > 0.01:
            sym_verdict = "LEAK-DOMINATED"
        elif abs(a_s - b_s) < abs(a_s) * 0.3 and abs(a_s - c_s) > abs(a_s) * 0.5:
            sym_verdict = "SKILL-CONFIRMED"
        elif c_s < b_s < a_s:
            sym_verdict = "PARTIAL-SKILL"
        else:
            sym_verdict = "INCONCLUSIVE"

        print(f"    {symbol:<8} A={a_s:+.4f} B={b_s:+.4f} C={c_s:+.4f} -> {sym_verdict}")

    elapsed = time.time() - t0

    # Save results: the pre-registered verdict on B is the one that counts.
    output = {
        "verdict": null_tests["B"]["verdict"],
        "null_test": null_tests,
        "leak_a_minus_b": leak,
        "threshold_verdict": verdict,
        "threshold_reason": reason,
        "aggregate": agg_table,
        "per_symbol": table,
        "per_symbol_seed": all_results,
        "config": {
            "symbols": symbols,
            "seeds": seeds,
            "n_splits": args.n_splits,
            "epochs_per_fold": args.epochs_per_fold,
            "d_model": args.d_model,
            "context_length": args.context_length,
            "window": args.window,
            "commission_bps": args.commission_bps,
            "n_null": args.n_null,
            "null": (
                "per condition and fold, draws shuffling the long-run lengths "
                "and the flat-run lengths among themselves, first state and "
                "alternation kept; p = (1 + draws >= T) / (1 + n_null) on "
                "seed means, Fisher over folds, Holm over symbols"
            ),
            "eval_protocol": CAUSAL_EVAL_PROTOCOL,
            "alignment": (
                "first decision at row window + context_length; decision k "
                "reads rows <= k-1 and drives return k -> k+1"
            ),
        },
        "elapsed_s": round(elapsed, 2),
        "device": device,
    }

    out_path = Path(args.output) if args.output else RESULTS_DIR / "results.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(output, indent=2, default=str), encoding="utf-8")
    # The draws themselves, so the p-values can be recomputed from the file.
    null_path = out_path.with_name(out_path.stem + "_null.npz")
    np.savez_compressed(null_path, **{
        f"{symbol}__s{seed}__{cond}__f{fold}": np.append(stat, null)
        for symbol, by_seed in null_store.items()
        for seed, by_cond in by_seed.items()
        for cond, by_fold in by_cond.items()
        for fold, (stat, null) in by_fold.items()
    })

    print(f"\nResults saved: {out_path}")
    print(f"Null draws saved (first value = condition Sharpe): {null_path}")
    print(f"Elapsed: {elapsed:.0f}s")


if __name__ == "__main__":
    main()
