"""Forecast table for the Cloud-VolTargeting vol-model experiment (issue #18921).

The protocol is pre-registered in issue #18921, comment 5964767205
(2026-10-03T02:44:26Z). This script implements its sections 2, 3, 5 and 6:

- daily variance proxy v_t = ln(O_t/C_{t-1})^2 + Garman-Klass_t
  (`realized_variance.daily_ohlc_variance`), taken in log;
- one forecast origin per rebalance date D (first session of each month):
  only sessions strictly before D are used, as in QuantConnect where the
  rebalance runs 30 min after the open of D;
- candidates `har` (log-HAR 1/5/22, expanding window, `HARModel`) and `tsfm`
  (TimesFM 2.5-200M zero-shot, context 512, horizon 21, mean of the path),
  both as the mean forecast log-variance over the next 21 sessions;
- baseline `rv21`: the code of `projects/Cloud-VolTargeting/main.py` as is
  (21 closes, 20 log returns, `np.std` with ddof=0, x sqrt(252));
- placebos: `har` forecasts permuted across rebalance dates, asset by asset,
  for 8 fixed seeds;
- forecast verdict: target = log of the mean proxy over sessions D..D+20
  (forecast steps 1..21 from the origin D-1), QLIKE and MSE(log), DM on the
  mse leg with the signed bias reported. Never merged with the strategy
  verdict, which is computed from the QuantConnect backtests.

Outputs (in `results/`): the forecast table (CSV), a JSON summary with the
forecast verdict, and the module `vol_forecasts.py` written into the QC
project so the backtests read the very same numbers.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd

sys.path.insert(0, str(Path(__file__).resolve().parent))

from dm_test import dm_verdict  # noqa: E402
from har_model import HARModel  # noqa: E402
from m18_tsfm_benchmark import TSFM_REPO_ID, TimesFMWrapper, qlike_loss  # noqa: E402
from realized_variance import daily_ohlc_variance, realized_variance_to_log  # noqa: E402

TICKERS = ["SPY", "QQQ", "IEF", "GLD"]
DATA_START = "2004-11-18"          # GLD inception: warm-up for HAR and the context
VERDICT_START = "2007-01-01"
VERDICT_END = "2026-08-31"
CONTAMINATION_START = "2025-01-01"  # reported apart, never decides the verdict
HORIZON = 21
CONTEXT_LEN = 512
RV21_CLOSES = 21                    # main.py: self.lookback = 21 closes
PLACEBO_SEEDS = [0, 1, 7, 42, 99, 123, 256, 1000]
TSFM_REPRO_TOL = 1e-6
PREREG = "issue #18921, comment 5964767205 (2026-10-03T02:44:26Z)"
QC_FILE_MAX_CHARS = 60_000          # QC rejects project files above 64,000 characters

RESULTS_DIR = Path(__file__).resolve().parent / "results"
QC_PROJECT_DIR = (Path(__file__).resolve().parents[2]
                  / "projects" / "Cloud-VolTargeting")


# ---------------------------------------------------------------------------
# Data
# ---------------------------------------------------------------------------

def load_ohlc(ticker: str, start: str, end: str, cache_dir: Path | None) -> pd.DataFrame:
    """Adjusted daily OHLC from yfinance (`auto_adjust=True`), cached as CSV."""
    if cache_dir is not None:
        path = cache_dir / f"{ticker}_{start}_{end}.csv"
        if path.exists():
            return pd.read_csv(path, index_col=0, parse_dates=True)
    import yfinance as yf

    df = yf.download(ticker, start=start, end=end, auto_adjust=True,
                     progress=False, actions=False)
    if isinstance(df.columns, pd.MultiIndex):
        df.columns = df.columns.get_level_values(0)
    df = df[["Open", "High", "Low", "Close"]].dropna()
    df.index = pd.DatetimeIndex(df.index).tz_localize(None).normalize()
    if df.empty:
        raise RuntimeError(f"no data downloaded for {ticker}")
    if cache_dir is not None:
        cache_dir.mkdir(parents=True, exist_ok=True)
        df.to_csv(path)
    return df


def panel_hash(panel: dict[str, pd.DataFrame]) -> str:
    h = hashlib.sha256()
    for t in sorted(panel):
        h.update(t.encode())
        h.update(np.ascontiguousarray(panel[t].to_numpy(dtype=float)).tobytes())
        h.update(np.asarray(panel[t].index.asi8).tobytes())
    return h.hexdigest()


# ---------------------------------------------------------------------------
# Protocol pieces (pure, unit-tested)
# ---------------------------------------------------------------------------

def rebalance_dates(sessions: pd.DatetimeIndex, start: str, end: str) -> list[pd.Timestamp]:
    """First session of each calendar month within [start, end]."""
    s = pd.DatetimeIndex(sessions).sort_values()
    s = s[(s >= pd.Timestamp(start)) & (s <= pd.Timestamp(end))]
    first = pd.Series(s, index=s).groupby([s.year, s.month]).min()
    return [pd.Timestamp(d) for d in first.to_numpy()]


def rv21_vol(closes_before: np.ndarray) -> float:
    """Replica of main.py: last 21 closes, std (ddof=0) of log returns x sqrt(252)."""
    closes = np.asarray(closes_before, dtype=float)[-RV21_CLOSES:]
    if len(closes) < RV21_CLOSES:
        raise ValueError(f"need {RV21_CLOSES} closes, got {len(closes)}")
    log_returns = np.log(closes[1:] / closes[:-1])
    return float(np.std(log_returns) * np.sqrt(252))


def vol_to_logvar(vol: float) -> float:
    """Annualized vol -> log of the daily variance it implies."""
    return float(np.log(vol ** 2 / 252.0))


def logvar_to_vol(logvar: np.ndarray | float) -> np.ndarray | float:
    """Mean forecast log daily variance -> annualized vol (pre-reg section 2)."""
    return np.sqrt(252.0 * np.exp(logvar))


def target_logvar(v: pd.Series, date: pd.Timestamp, horizon: int = HORIZON) -> float:
    """log of the mean proxy over the `horizon` sessions starting at `date`."""
    window = v[v.index >= date].iloc[:horizon]
    if len(window) < horizon:
        return float("nan")
    return float(np.log(window.mean()))


def har_logvar(v_hist: pd.Series, horizon: int = HORIZON) -> float:
    """Expanding-window log-HAR, mean forecast log-variance over `horizon` steps."""
    model = HARModel().fit(v_hist)
    return model.predict_h_step(v_hist, horizon)


def placebo_logvar(har: pd.DataFrame, seed: int) -> pd.DataFrame:
    """Permute each asset's `har` forecasts across rebalance dates.

    One generator per seed, one permutation per asset, assets in column order:
    the per-asset distribution is kept, the timing is destroyed.
    """
    rng = np.random.default_rng(seed)
    out = har.copy()
    for col in har.columns:
        out[col] = har[col].to_numpy()[rng.permutation(len(har))]
    return out


def tsfm_logvar(log_v: dict[str, np.ndarray], origins: dict[str, list[int]],
                tsfm: TimesFMWrapper, horizon: int = HORIZON) -> dict[str, np.ndarray]:
    """One batched TimesFM call over every (asset, origin) context."""
    keys, contexts = [], []
    for t in log_v:
        for i in origins[t]:
            keys.append(t)
            contexts.append(log_v[t][max(0, i - tsfm.context_len):i].astype(np.float32))
    point, _ = tsfm.forecast_paths(contexts, horizon)
    means = point[:, :horizon].mean(axis=1)
    out: dict[str, list[float]] = {t: [] for t in log_v}
    for k, m in zip(keys, means):
        out[k].append(float(m))
    return {t: np.asarray(vals) for t, vals in out.items()}


# ---------------------------------------------------------------------------
# Forecast verdict (pre-reg section 5)
# ---------------------------------------------------------------------------

def compare(model: np.ndarray, base: np.ndarray, target: np.ndarray) -> dict:
    e_m, e_b = model - target, base - target
    dm = dm_verdict(e_m, e_b, loss_fn="mse", horizon=1)
    return {
        "n": int(len(target)),
        "mse_log_model": float(np.mean(e_m ** 2)),
        "mse_log_base": float(np.mean(e_b ** 2)),
        "qlike_model": qlike_loss(np.exp(target), np.exp(model)),
        "qlike_base": qlike_loss(np.exp(target), np.exp(base)),
        "bias_model": float(np.mean(e_m)),
        "bias_base": float(np.mean(e_b)),
        # descriptive only (pre-reg: no debiasing): MSE = bias^2 + centered MSE
        "centered_mse_model": float(np.var(e_m)),
        "centered_mse_base": float(np.var(e_b)),
        "dm_stat": float(dm["dm_statistic"]),
        "dm_p": float(dm["p_value"]),
        "mean_loss_diff": float(dm["mean_loss_diff"]),
    }


def pair_verdict(per_asset: dict[str, dict]) -> str:
    """Strict reading of section 5: p < 0.05 AND the same sign on all 4 assets."""
    sig = [r["dm_p"] < 0.05 for r in per_asset.values()]
    diffs = [r["mean_loss_diff"] for r in per_asset.values()]
    if all(sig) and all(d < 0 for d in diffs):
        return "BEATS"
    if all(sig) and all(d > 0 for d in diffs):
        return "BEATEN"
    return "INCONCLUSIVE"


def pooled_dm(models: dict[str, np.ndarray], bases: dict[str, np.ndarray],
              targets: dict[str, np.ndarray]) -> dict:
    """Secondary reading: DM on the cross-asset mean loss differential."""
    d = np.mean([(models[t] - targets[t]) ** 2 - (bases[t] - targets[t]) ** 2
                 for t in targets], axis=0)
    dm = dm_verdict(d, np.zeros_like(d), loss_fn="linear", horizon=1)
    return {"mean_loss_diff": float(np.mean(d)), "dm_stat": float(dm["dm_statistic"]),
            "dm_p": float(dm["p_value"])}


def forecast_verdict(table: pd.DataFrame, since: str | None = None) -> dict:
    sub = table if since is None else table[table["date"] >= pd.Timestamp(since)]
    pairs = {"har_vs_rv21": ("har_logvar", "rv21_logvar"),
             "tsfm_vs_rv21": ("tsfm_logvar", "rv21_logvar"),
             "tsfm_vs_har": ("tsfm_logvar", "har_logvar")}
    out = {}
    for name, (m, b) in pairs.items():
        per_asset, models, bases, targets = {}, {}, {}, {}
        for t in TICKERS:
            g = sub[sub["ticker"] == t].dropna(subset=[m, b, "target_logvar"])
            models[t], bases[t] = g[m].to_numpy(), g[b].to_numpy()
            targets[t] = g["target_logvar"].to_numpy()
            per_asset[t] = compare(models[t], bases[t], targets[t])
        out[name] = {"verdict": pair_verdict(per_asset), "per_asset": per_asset,
                     "pooled_secondary": pooled_dm(models, bases, targets)}
    return out


# ---------------------------------------------------------------------------
# QC embedding
# ---------------------------------------------------------------------------

def write_qc_module(table: pd.DataFrame, path: Path, meta: dict,
                    max_chars: int = QC_FILE_MAX_CHARS) -> list[Path]:
    """Write the vols the backtests read, keyed by rebalance date and asset.

    QuantConnect rejects project files above 64,000 characters, so the models
    are packed into `<stem>_partK.py` files under `max_chars`; `path` holds
    DATES and re-assembles FORECASTS from the parts. Returns the files written,
    `path` first. Stale parts from a previous run are removed.
    """
    dates = sorted(table["date"].unique())
    models = {"rv21_offqc": "rv21_logvar", "har": "har_logvar", "tsfm": "tsfm_logvar"}
    models.update({f"placebo_{s}": f"placebo_{s}_logvar" for s in PLACEBO_SEEDS})
    header = [
        "# Generated by ML-Training-Pipeline/scripts/voltarget_forecasts.py -- do not edit.",
        f"# Pre-registration: {PREREG}.",
        f"# Panel sha256: {meta['panel_sha256']}; TimesFM revision: {meta['tsfm_revision']}.",
        "# Annualized vol forecast per rebalance date (first session of the month).",
    ]
    blocks = []
    for name, col in models.items():
        lines = [f'    "{name}": {{']
        for t in TICKERS:
            g = table[table["ticker"] == t].set_index("date").reindex(dates)
            vols = logvar_to_vol(g[col].to_numpy())
            lines.append(f'        "{t}": [' + ", ".join(f"{x:.6g}" for x in vols) + "],")
        lines.append("    },")
        blocks.append("\n".join(lines))

    overhead = sum(len(h) + 1 for h in header) + 64
    parts: list[list[str]] = [[]]
    for b in blocks:
        if parts[-1] and overhead + sum(len(x) + 1 for x in parts[-1]) + len(b) > max_chars:
            parts.append([])
        parts[-1].append(b)

    for old in path.parent.glob(f"{path.stem}_part*.py"):
        old.unlink()
    written, imports = [path], []
    for k, part in enumerate(parts, 1):
        p = path.with_name(f"{path.stem}_part{k}.py")
        text = "\n".join(header + [f"# Part {k}/{len(parts)} of {path.name}.", "",
                                   "FORECASTS = {", *part, "}"]) + "\n"
        if len(text) > max_chars:
            raise ValueError(f"{p.name}: {len(text)} characters > {max_chars}")
        p.write_text(text, encoding="utf-8", newline="\n")
        written.append(p)
        imports.append(f"from {p.stem} import FORECASTS as _part{k}")
    text = "\n".join(header + [
        "",
        "DATES = [" + ", ".join(f'"{pd.Timestamp(d):%Y-%m-%d}"' for d in dates) + "]",
        "",
        *imports,
        "",
        "FORECASTS = {" + ", ".join(f"**_part{k}" for k in range(1, len(parts) + 1)) + "}",
    ]) + "\n"
    if len(text) > max_chars:
        raise ValueError(f"{path.name}: {len(text)} characters > {max_chars}")
    path.write_text(text, encoding="utf-8", newline="\n")
    return written


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def load_tsfm(attempts: int = 5, wait_s: float = 5.0) -> TimesFMWrapper:
    """Production loader, retried on a failed provenance lookup (flaky network).

    Only the same lookup is retried: after `attempts` failures the error is
    raised, never replaced by another model (#14768).
    """
    import time

    for k in range(attempts):
        try:
            return TimesFMWrapper.production_loader(TSFM_REPO_ID, CONTEXT_LEN)
        except RuntimeError as exc:
            if "provenance lookup failed" not in str(exc) or k == attempts - 1:
                raise
            time.sleep(wait_s)
    raise AssertionError("unreachable")


def build_table(panel: dict[str, pd.DataFrame], tsfm: TimesFMWrapper | None,
                tsfm_runs: int = 2) -> tuple[pd.DataFrame, dict]:
    sessions = panel["SPY"].index
    dates = rebalance_dates(sessions, VERDICT_START, VERDICT_END)
    v = {t: daily_ohlc_variance(panel[t]) for t in TICKERS}
    rows, origins, log_v = [], {}, {}
    zero_days = {t: int((v[t] <= 0).sum()) for t in TICKERS}
    for t in TICKERS:
        log_v[t] = realized_variance_to_log(v[t]).to_numpy()
        origins[t] = []
        closes = panel[t]["Close"]
        for d in dates:
            hist = v[t][v[t].index < d]
            rv21 = rv21_vol(closes[closes.index < d].to_numpy())
            rows.append({
                "date": d, "ticker": t,
                "origin": hist.index[-1],
                "rv21_vol_offqc": rv21,
                "rv21_logvar": vol_to_logvar(rv21),
                "har_logvar": har_logvar(hist),
                "target_logvar": target_logvar(v[t], d),
            })
            origins[t].append(len(hist))
    table = pd.DataFrame(rows)
    meta: dict = {"zero_variance_days": zero_days, "n_rebalances": len(dates)}
    if tsfm is not None:
        runs = [tsfm_logvar(log_v, origins, tsfm) for _ in range(tsfm_runs)]
        for k, run in enumerate(runs):
            col = "tsfm_logvar" if k == 0 else f"tsfm_logvar_run{k + 1}"
            table[col] = np.concatenate([run[t] for t in TICKERS])
        if tsfm_runs > 1:
            diff = max(float(np.max(np.abs(runs[0][t] - runs[1][t]))) for t in TICKERS)
            meta["tsfm_run_max_abs_diff"] = diff
            meta["tsfm_reproducible"] = diff <= TSFM_REPRO_TOL
    har_wide = table.pivot(index="date", columns="ticker", values="har_logvar")[TICKERS]
    for s in PLACEBO_SEEDS:
        perm = placebo_logvar(har_wide, s).stack().rename(f"placebo_{s}_logvar")
        table = table.merge(perm.reset_index(), on=["date", "ticker"], how="left")
    return table, meta


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--end", default="2026-10-01",
                    help="exclusive download end (must cover 21 sessions after the last rebalance)")
    ap.add_argument("--cache-dir", type=Path, default=None,
                    help="optional OHLC cache directory (kept outside the repository)")
    ap.add_argument("--out-dir", type=Path, default=RESULTS_DIR)
    ap.add_argument("--qc-module", type=Path, default=QC_PROJECT_DIR / "vol_forecasts.py")
    ap.add_argument("--qc-module-only", action="store_true",
                    help="rewrite the QC module from the CSV and JSON already in --out-dir "
                         "(no download, no TimesFM)")
    args = ap.parse_args()

    if args.qc_module_only:
        table = pd.read_csv(args.out_dir / "voltarget_forecasts.csv", parse_dates=["date"])
        meta = json.loads((args.out_dir / "voltarget_forecasts_summary.json")
                          .read_text(encoding="utf-8"))
        for p in write_qc_module(table, args.qc_module, meta):
            print(f"{p.name}: {len(p.read_text(encoding='utf-8'))} characters")
        return

    panel = {t: load_ohlc(t, DATA_START, args.end, args.cache_dir) for t in TICKERS}
    common = panel["SPY"].index
    for t in TICKERS:
        common = common.intersection(panel[t].index)
    panel = {t: panel[t].loc[common] for t in TICKERS}

    tsfm = load_tsfm()
    table, meta = build_table(panel, tsfm)
    meta.update({
        "preregistration": PREREG,
        "panel_sha256": panel_hash(panel),
        "panel_first": f"{common[0]:%Y-%m-%d}", "panel_last": f"{common[-1]:%Y-%m-%d}",
        "tsfm_repo_id": TSFM_REPO_ID, "tsfm_revision": tsfm.revision,
        "tsfm_series_served": tsfm.n_calls,
        "verdict_block": [VERDICT_START, VERDICT_END],
        "forecast_verdict": forecast_verdict(table),
        "forecast_contamination_subblock": forecast_verdict(table, CONTAMINATION_START),
    })

    args.out_dir.mkdir(parents=True, exist_ok=True)
    table.to_csv(args.out_dir / "voltarget_forecasts.csv", index=False, float_format="%.8g",
                 date_format="%Y-%m-%d")
    (args.out_dir / "voltarget_forecasts_summary.json").write_text(
        json.dumps(meta, indent=2, default=str) + "\n", encoding="utf-8")
    write_qc_module(table, args.qc_module, meta)
    print(json.dumps({k: meta[k] for k in ("n_rebalances", "zero_variance_days",
                                           "tsfm_run_max_abs_diff", "panel_sha256")}, indent=2))
    for name, res in meta["forecast_verdict"].items():
        print(name, res["verdict"], {t: round(r["dm_p"], 4) for t, r in res["per_asset"].items()})


if __name__ == "__main__":
    main()
