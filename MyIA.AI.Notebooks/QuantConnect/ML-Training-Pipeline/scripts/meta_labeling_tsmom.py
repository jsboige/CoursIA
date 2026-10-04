"""Meta-labeling of the 12-month TSMOM rule on the ETF basket -- experiment 5b, issue #18922.

Pre-registration: issue #18922, comment 5974356727 (2026-10-03T22:55:40Z).
Every constant below is fixed there; changing one after the first computation
opens a new experiment.

Primary rule (no ML), decided at the close of each month's last session:
sign of the 252-session return (``L1_tsmom.compute_tsmom_signal``) times the
63-session volatility scale (``L1_tsmom.compute_vol_scale``, 15 % target),
normalised by the sum of scales over eligible assets (gross exposure 1).
Positions are held to the next decision and drift with prices; 5 bps on the
notional traded at each rebalance.

Secondary model: a random forest that estimates, for each (asset, decision)
event, the probability that the position is a winner under a triple-barrier
label (+-2 sigma_63 sqrt(H), time barrier = next decision). Two variants:
``filter`` keeps a position when p > 0.5, ``size`` scales it by p. The weight
removed stays in cash.

Strategy verdict: Sharpe(variant) - Sharpe(primary) on the frozen block
2022-01-03..2026-09-30, paired circular block bootstrap and Holm from
``voltarget_strategy_verdict`` (experiment 5a), against 8 month-block label
permutations (placebo). Forecast verdict, reported apart: Brier score against
the development base rate, Diebold-Mariano test (``diebold_mariano``).

Outputs the aggregate JSON on stdout; ``--out-dir`` also writes
``meta_labeling_tsmom.json`` (committed) and ``--series-dir`` the daily series
and per-event probabilities (kept outside the repository).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from L1_tsmom import compute_tsmom_signal, compute_vol_scale  # noqa: E402
from diebold_mariano import diebold_mariano_test  # noqa: E402
from panier_loader import PANIER_GROUPS, ensure_symbol  # noqa: E402
from voltarget_strategy_verdict import _sharpe, circular_block_diff, holm  # noqa: E402

ASSET_CLASSES = {
    "broad": PANIER_GROUPS["us_equity_broad"],
    "sector": PANIER_GROUPS["us_equity_sectors"],
    "bond": PANIER_GROUPS["us_bonds"],
    "commodity": PANIER_GROUPS["commodities"],
    "intl": PANIER_GROUPS["international"],
}
SYMBOLS = [s for group in ASSET_CLASSES.values() for s in group]
VIX = "VIX"
DATA_START, DATA_END = "2015-01-01", "2026-10-01"

LOOKBACK, VOL_WINDOW, TARGET_VOL, MA_WINDOW = 252, 63, 0.15, 200
BARRIER_K = 2.0
FEE_RATE = 5.0 / 10_000
DEV_FIRST, DEV_LAST, DEV_LABEL_END = "2016-01-29", "2021-11-30", "2021-12-31"
BLOCK_FIRST_DECISION, BLOCK_LAST_DECISION = "2021-12-31", "2026-08-31"
BLOCK_START, BLOCK_END = "2022-01-03", "2026-09-30"

SEEDS = [0, 1, 7, 42, 99, 123, 256, 1000]
PLACEBO_SEEDS = SEEDS
GRID = [{"max_depth": d, "min_samples_leaf": leaf} for d in (3, 5) for leaf in (25, 50)]
N_TREES = 500
CV_FOLDS, EMBARGO = 5, 21
DM_H = 21
VARIANTS = ["filter", "size"]
SEED_SIGN_MIN = 7
FEATURES = ["side", "r21", "r63", "r126", "r252", "vol63", "vol_ratio", "ma200_gap",
            "vix", "vix_chg21", "breadth"] + [f"cls_{c}" for c in ASSET_CLASSES]
TRADING_DAYS = 252


# --------------------------------------------------------------------------- data

def load_closes(data_dir: Path) -> tuple[pd.DataFrame, pd.Series]:
    """ETF closes on the SPY session calendar (NaN before listing) and the VIX."""
    frames = {}
    for sym in SYMBOLS + [VIX]:
        path = ensure_symbol(sym, start=DATA_START, end=DATA_END, panier_dir=data_dir)
        if path is None:
            raise RuntimeError(f"no data for {sym}")
        frames[sym] = pd.read_csv(path, index_col=0, parse_dates=True)["Close"]
    sessions = frames["SPY"].dropna().index
    if sessions[-1] != pd.Timestamp(BLOCK_END):
        raise RuntimeError(f"data end {sessions[-1]:%Y-%m-%d}, expected {BLOCK_END}")
    closes = pd.DataFrame({s: frames[s].reindex(sessions) for s in SYMBOLS})
    vix = frames[VIX].reindex(sessions).ffill()
    return closes, vix


def panel_digest(closes: pd.DataFrame) -> str:
    """sha256 of the close matrix, rounded to 6 decimals (CSV, NaN as empty)."""
    text = closes.round(6).to_csv(float_format="%.6f")
    return hashlib.sha256(text.encode()).hexdigest()


def decision_dates(sessions: pd.DatetimeIndex) -> pd.DatetimeIndex:
    """The last session of each month."""
    s = sessions.to_series()
    return pd.DatetimeIndex(s.groupby(sessions.to_period("M")).max().to_numpy())


# --------------------------------------------------------------- events and labels

def triple_barrier(path: np.ndarray, barrier: float) -> int:
    """1 if +barrier is hit first, 0 if -barrier is; else the sign of the last value."""
    for value in path:
        if value >= barrier:
            return 1
        if value <= -barrier:
            return 0
    return int(path[-1] > 0)


def build_events(closes: pd.DataFrame, vix: pd.Series) -> tuple[pd.DataFrame, dict]:
    """One row per (asset, decision) with a non-zero sign and a next decision.

    Returns the events (features, label, primary weight, window end) and the
    primary weights per decision (all eligible assets, zero-sign included).
    """
    sessions = closes.index
    pos = {d: i for i, d in enumerate(sessions)}
    decisions = decision_dates(sessions)
    per_asset = {}
    for sym in SYMBOLS:
        c = closes[sym].dropna()
        r = c.pct_change()
        per_asset[sym] = pd.DataFrame({
            "close": c,
            "count": np.arange(1, len(c) + 1),
            "side": compute_tsmom_signal(c, LOOKBACK),
            "scale": compute_vol_scale(c, VOL_WINDOW, TARGET_VOL),
            "r21": c.pct_change(21), "r63": c.pct_change(63),
            "r126": c.pct_change(126), "r252": c.pct_change(LOOKBACK),
            "sd21": r.rolling(21).std(), "sd63": r.rolling(VOL_WINDOW).std(),
            "ma200": c.rolling(MA_WINDOW).mean(),
        })
    vix_chg = np.log(vix / vix.shift(21))
    cls_of = {s: c for c, group in ASSET_CLASSES.items() for s in group}

    rows, weights = [], {}
    for k, t in enumerate(decisions[:-1]):
        t_next = decisions[k + 1]
        snap = {s: per_asset[s].loc[t] for s in SYMBOLS if t in per_asset[s].index}
        eligible = {s: v for s, v in snap.items() if v["count"] > LOOKBACK}
        if not eligible:
            continue
        scale_sum = sum(v["scale"] for v in eligible.values())
        weights[t] = pd.Series({s: v["side"] * v["scale"] / scale_sum
                                for s, v in eligible.items()}, dtype=float)
        breadth = float(np.mean([v["r252"] > 0 for v in eligible.values()]))
        window = sessions[pos[t] + 1: pos[t_next] + 1]
        for s, v in eligible.items():
            side = v["side"]
            if side == 0:
                continue
            path = side * (closes.loc[window, s].to_numpy() / v["close"] - 1.0)
            barrier = BARRIER_K * v["sd63"] * math.sqrt(len(window))
            row = {"date": t, "end": t_next, "asset": s, "side": side,
                   "weight": weights[t][s], "label": triple_barrier(path, barrier),
                   "ret_signed": float(path[-1]),
                   "r21": side * v["r21"], "r63": side * v["r63"],
                   "r126": side * v["r126"], "r252": side * v["r252"],
                   "vol63": v["sd63"] * math.sqrt(TRADING_DAYS),
                   "vol_ratio": v["sd21"] / v["sd63"],
                   "ma200_gap": side * (v["close"] / v["ma200"] - 1.0),
                   "vix": float(vix.loc[t]), "vix_chg21": float(vix_chg.loc[t]),
                   "breadth": breadth}
            for c in ASSET_CLASSES:
                row[f"cls_{c}"] = int(cls_of[s] == c)
            rows.append(row)
    events = pd.DataFrame(rows).sort_values(["date", "asset"]).reset_index(drop=True)
    return events, weights


def split_events(events: pd.DataFrame) -> tuple[pd.DataFrame, pd.DataFrame]:
    dev = events[(events["date"] >= DEV_FIRST) & (events["date"] <= DEV_LAST)
                 & (events["end"] <= DEV_LABEL_END)]
    block = events[(events["date"] >= BLOCK_FIRST_DECISION)
                   & (events["date"] <= BLOCK_LAST_DECISION)]
    return dev.reset_index(drop=True), block.reset_index(drop=True)


# ------------------------------------------------------------------------ model

def make_model(config: dict, seed: int):
    from sklearn.ensemble import RandomForestClassifier
    return RandomForestClassifier(n_estimators=N_TREES, max_features="sqrt",
                                  random_state=seed, n_jobs=-1, **config)


def purged_folds(dev: pd.DataFrame, sessions: pd.DatetimeIndex,
                 n_folds: int = CV_FOLDS, embargo: int = EMBARGO) -> list:
    """Contiguous folds over decision dates; purge training events whose label
    window [date, end] meets the test span widened by ``embargo`` sessions."""
    pos = {d: i for i, d in enumerate(sessions)}
    dates = np.array(sorted(dev["date"].unique()))
    folds = []
    for group in np.array_split(dates, n_folds):
        test = dev["date"].isin(group).to_numpy()
        lo = sessions[max(0, pos[pd.Timestamp(group[0])] - embargo)]
        hi_end = dev.loc[test, "end"].max()
        hi = sessions[min(len(sessions) - 1, pos[hi_end] + embargo)]
        overlap = (dev["date"] <= hi) & (dev["end"] >= lo)
        train = (~test) & (~overlap.to_numpy())
        folds.append((np.flatnonzero(train), np.flatnonzero(test)))
    return folds


def log_loss(y: np.ndarray, p: np.ndarray) -> float:
    p = np.clip(p, 1e-12, 1 - 1e-12)
    return float(-np.mean(y * np.log(p) + (1 - y) * np.log(1 - p)))


def select_config(dev: pd.DataFrame, sessions: pd.DatetimeIndex) -> tuple[dict, list]:
    """Grid point with the lowest pooled out-of-fold log loss, mean over seeds."""
    X, y = dev[FEATURES].to_numpy(), dev["label"].to_numpy()
    folds = purged_folds(dev, sessions)
    scores = []
    for config in GRID:
        per_seed = []
        for seed in SEEDS:
            oof = np.full(len(y), np.nan)
            for train, test in folds:
                model = make_model(config, seed).fit(X[train], y[train])
                oof[test] = model.predict_proba(X[test])[:, 1]
            per_seed.append(log_loss(y, oof))
        scores.append({**config, "oof_log_loss": round(float(np.mean(per_seed)), 6)})
    best = min(range(len(GRID)), key=lambda i: scores[i]["oof_log_loss"])
    return GRID[best], scores


def fit_predict(dev: pd.DataFrame, block: pd.DataFrame, config: dict, seed: int,
                labels: np.ndarray | None = None) -> np.ndarray:
    y = dev["label"].to_numpy() if labels is None else labels
    model = make_model(config, seed).fit(dev[FEATURES].to_numpy(), y)
    return model.predict_proba(block[FEATURES].to_numpy())[:, 1]


def month_block_permutation(dev: pd.DataFrame, seed: int) -> np.ndarray:
    """Dev labels with each month's labels kept together and the month order shuffled."""
    blocks = [g["label"].to_numpy() for _, g in dev.groupby("date", sort=True)]
    order = np.random.default_rng(seed).permutation(len(blocks))
    return np.concatenate([blocks[i] for i in order])


# ------------------------------------------------------------------- portfolio

def variant_weights(weights: dict, block: pd.DataFrame, p: np.ndarray | None,
                    variant: str | None) -> dict:
    """Primary weights of the block decisions, filtered or sized by ``p``."""
    out = {}
    factor = pd.Series(1.0, index=block.index)
    if variant == "filter":
        factor = pd.Series((p > 0.5).astype(float), index=block.index)
    elif variant == "size":
        factor = pd.Series(p, index=block.index)
    for t in sorted(weights):
        if not pd.Timestamp(BLOCK_FIRST_DECISION) <= t <= pd.Timestamp(BLOCK_LAST_DECISION):
            continue
        w = weights[t].copy()
        for idx in block.index[block["date"] == t]:
            w[block.at[idx, "asset"]] = block.at[idx, "weight"] * factor[idx]
        out[t] = w
    return out


def simulate(closes: pd.DataFrame, weights: dict, end: str = BLOCK_END) -> pd.DataFrame:
    """Drifting holdings, rebalanced at each decision close, fees on traded notional.

    Returns per session from the first decision: net return, turnover (traded
    notional / equity) and fees (fraction of the starting equity).
    """
    rets = closes.pct_change(fill_method=None).fillna(0.0)
    decisions = sorted(weights)
    sessions = closes.index[(closes.index >= decisions[0]) & (closes.index <= end)]
    v = pd.Series(0.0, index=closes.columns)
    equity, records = 1.0, []
    for d in sessions:
        prev = equity
        r = rets.loc[d]
        equity += float((v * r).sum())
        v = v * (1.0 + r)
        turnover = fee = 0.0
        if d in weights:
            target = weights[d].reindex(closes.columns).fillna(0.0)
            turnover = float((target - v / equity).abs().sum())
            fee = FEE_RATE * turnover * equity
            equity -= fee
            v = target * equity
        records.append((d, equity / prev - 1.0, turnover, fee))
    out = pd.DataFrame(records, columns=["date", "net_return", "turnover", "fee"])
    return out.set_index("date")


def series_stats(sim: pd.DataFrame) -> dict:
    """Sharpe, CAGR and drawdown as in experiment 5a; fees include the entry."""
    rets = sim.loc[BLOCK_START:BLOCK_END, "net_return"]
    years = (rets.index[-1] - rets.index[0]).days / 365.25
    wealth = (1.0 + rets).cumprod()
    return {"n_days": int(len(rets)),
            "sharpe": round(float(_sharpe(rets.to_numpy())), 4),
            "cagr": round(float(wealth.iloc[-1] ** (1.0 / years) - 1.0), 4),
            "max_drawdown": round(float((wealth / wealth.cummax() - 1.0).min()), 4),
            "turnover_mean": round(float(sim.loc[BLOCK_START:BLOCK_END, "turnover"].mean()), 6),
            "fees": round(float(sim["fee"].sum()), 6)}


def block_returns(sim: pd.DataFrame) -> pd.Series:
    return sim.loc[BLOCK_START:BLOCK_END, "net_return"]


# --------------------------------------------------------------------- verdicts

def strategy_gate(diff: float, p_holm: float, placebo_max: float, seeds_positive: int) -> str:
    """Pre-registration section 6."""
    if diff <= 0:
        return "NO BEATS"
    if p_holm < 0.05 and diff > placebo_max and seeds_positive >= SEED_SIGN_MIN:
        return "BEATS"
    return "INCONCLUSIVE"


def forecast_verdict(y: np.ndarray, probs: dict, base_rate: float) -> dict:
    """Pre-registration section 7: Brier edge over the base rate, DM per seed."""
    from sklearn.metrics import roc_auc_score
    base = np.full(len(y), base_rate)
    brier_base = float(np.mean((y - base) ** 2))
    per_seed, edges, p_less, p_greater = {}, [], [], []
    for seed, p in probs.items():
        brier = float(np.mean((y - p) ** 2))
        edge = brier_base - brier
        dm_less = diebold_mariano_test(y - p, y - base, loss_function="squared",
                                       alternative="less", h=DM_H)
        dm_greater = diebold_mariano_test(y - p, y - base, loss_function="squared",
                                          alternative="greater", h=DM_H)
        hits = p > 0.5
        per_seed[str(seed)] = {
            "brier": round(brier, 6), "edge": round(edge, 6),
            "dm_stat": round(float(dm_less["dm_stat"]), 4),
            "dm_p_less": round(float(dm_less["p_value"]), 4),
            "auc": round(float(roc_auc_score(y, p)), 4),
            "precision_p_gt_half": (round(float(y[hits].mean()), 4) if hits.any() else None),
            "share_p_gt_half": round(float(hits.mean()), 4),
            "bias_mean_p_minus_y": round(float(np.mean(p - y)), 4)}
        edges.append(edge)
        p_less.append(dm_less["p_value"])
        p_greater.append(dm_greater["p_value"])
    mean, sd = float(np.mean(edges)), float(np.std(edges, ddof=1))
    med_less, med_greater = float(np.median(p_less)), float(np.median(p_greater))
    if mean > 0 and mean >= 2 * sd and med_less < 0.05:
        verdict = "prévision BEATS"
    elif mean < 0 and -mean >= 2 * sd and med_greater < 0.05:
        verdict = "prévision BEATEN"
    else:
        verdict = "INCONCLUSIVE"
    return {"n_events": int(len(y)), "base_rate": round(base_rate, 4),
            "label_rate_block": round(float(y.mean()), 4),
            "brier_base": round(brier_base, 6), "edge_mean": round(mean, 6),
            "edge_sd": round(sd, 6), "dm_p_median_less": round(med_less, 4),
            "dm_p_median_greater": round(med_greater, 4), "verdict": verdict,
            "per_seed": per_seed}


# ------------------------------------------------------------------------- main

def run(data_dir: Path, series_dir: Path | None) -> dict:
    closes, vix = load_closes(data_dir)
    events, weights = build_events(closes, vix)
    dev, block = split_events(events)
    config, grid_scores = select_config(dev, closes.index)

    probs = {seed: fit_predict(dev, block, config, seed) for seed in SEEDS}
    p_mean = np.mean(list(probs.values()), axis=0)
    primary = simulate(closes, variant_weights(weights, block, None, None))
    sims = {"primary": primary}
    for v in VARIANTS:
        sims[v] = simulate(closes, variant_weights(weights, block, p_mean, v))
    primary_sharpe = float(_sharpe(block_returns(primary).to_numpy()))

    per_seed = {v: {} for v in VARIANTS}
    for seed, p in probs.items():
        for v in VARIANTS:
            sim = simulate(closes, variant_weights(weights, block, p, v))
            per_seed[v][str(seed)] = round(
                float(_sharpe(block_returns(sim).to_numpy())) - primary_sharpe, 4)

    placebo = {v: {} for v in VARIANTS}
    for seed in PLACEBO_SEEDS:
        p = fit_predict(dev, block, config, seed, labels=month_block_permutation(dev, seed))
        for v in VARIANTS:
            sim = simulate(closes, variant_weights(weights, block, p, v))
            placebo[v][str(seed)] = round(
                float(_sharpe(block_returns(sim).to_numpy())) - primary_sharpe, 4)

    boots = {v: circular_block_diff(block_returns(sims[v]), block_returns(primary))
             for v in VARIANTS}
    adjusted = holm({v: boots[v]["p_one_sided"] for v in VARIANTS})
    strategy = {}
    for v in VARIANTS:
        b = boots[v]
        placebo_max = max(placebo[v].values())
        positive = sum(d > 0 for d in per_seed[v].values())
        strategy[v] = {"diff": round(b["observed"], 4), "p_raw": round(b["p_one_sided"], 4),
                       "p_holm": round(adjusted[v], 4),
                       "ci95": [round(x, 4) for x in b["ci95"]],
                       "placebo_max_diff": placebo_max, "seeds_positive": positive,
                       "verdict": strategy_gate(b["observed"], adjusted[v],
                                                placebo_max, positive)}

    y_block = block["label"].to_numpy()
    forecast = forecast_verdict(y_block, probs, float(dev["label"].mean()))

    if series_dir is not None:
        series_dir.mkdir(parents=True, exist_ok=True)
        pd.DataFrame({k: s["net_return"] for k, s in sims.items()}).to_csv(
            series_dir / "meta_labeling_tsmom_daily.csv")
        out = block[["date", "asset", "side", "weight", "label", "ret_signed"]].copy()
        for seed, p in probs.items():
            out[f"p_{seed}"] = p
        out.to_csv(series_dir / "meta_labeling_tsmom_events.csv", index=False)

    return {
        "experiment": "5b (#18922)",
        "preregistration": "issue #18922, comment 5974356727 (2026-10-03T22:55:40Z)",
        "data": {"symbols": SYMBOLS, "first": f"{closes.index[0]:%Y-%m-%d}",
                 "last": f"{closes.index[-1]:%Y-%m-%d}",
                 "closes_sha256": panel_digest(closes)},
        "events": {"dev": int(len(dev)), "block": int(len(block)),
                   "dev_label_rate": round(float(dev["label"].mean()), 4)},
        "selection": {"chosen": config, "grid": grid_scores},
        "series": {k: series_stats(s) for k, s in sims.items()},
        "strategy": strategy,
        "strategy_per_seed_diff": per_seed,
        "placebo_diff": placebo,
        "forecast": forecast,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--data-dir", type=Path, required=True,
                        help="directory of the basket CSVs (downloaded when missing)")
    parser.add_argument("--out-dir", type=Path, help="write meta_labeling_tsmom.json here")
    parser.add_argument("--series-dir", type=Path,
                        help="write daily series and per-event probabilities here")
    args = parser.parse_args()
    result = run(args.data_dir, args.series_dir)
    text = json.dumps(result, indent=2, ensure_ascii=False)
    print(text)
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / "meta_labeling_tsmom.json").write_text(text + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
